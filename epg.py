#!/usr/bin/env python3
"""
Genera una EPG en formato XMLTV a partir de las parrillas de TVTV.us.

Fuente: https://www.tvtv.us  (endpoints htmx internos, sin navegador)

Flujo:
  1. /partial/lineup/{lineup}            -> canales (station id, numero, callsign, logo)
  2. /partial/source/{ts}/{stationId}    -> programacion de un dia para un canal
  3. /dlg/program?id=&time=              -> ficha: genero, sinopsis, poster (cacheado)
  4. genera XMLTV (tv/channel/programme) con horarios en UTC

Solo usa la libreria estandar de Python.
"""

from __future__ import annotations

import argparse
import concurrent.futures as futures
import datetime as dt
import gzip
import html as html_mod
import json
import os
import random
import re
import sys
import time
import unicodedata
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any, Iterable
from xml.sax.saxutils import escape, quoteattr

# --------------------------------------------------------------------------- #
# Configuracion
# --------------------------------------------------------------------------- #

DEFAULT_CONFIG: dict[str, Any] = {
    "source": {
        "base_url": "https://www.tvtv.us",
        "lineup_path": "/pr/san-juan/00901/luUSA-PR00811-X",
        "lineup_id": "USA-PR00811-X",
        "language": "es",
        "user_agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36"
        ),
    },
    "output": {
        "file": "epg.xml",
        "generator": "tvtv-epg-builder",
        "id_prefix": "liberty",
        "include_icons": True,
        "exclude_channel_patterns": [],
        "channel_name_template": "{number} {name}",
    },
    "fetch": {
        "days_back": 1,
        "days_forward": 7,
        "workers": 5,
        "timeout": 30,
        "retries": 3,
        "delay_between_days": 0.25,
        "details": True,
        "details_interval": 1.2,
        "details_budget": 600,
        "details_cooldown_hours": 6,
    },
    "validation": {
        "min_channels": 50,
        "min_programmes": 1000,
        "max_empty_channel_ratio": 0.5,
    },
}

HEADERS_EXTRA = {
    "Accept": "*/*",
    "Accept-Language": "en-US,en;q=0.9,es;q=0.8",
    "Sec-Fetch-Dest": "empty",
    "Sec-Fetch-Mode": "cors",
    "Sec-Fetch-Site": "same-origin",
}


def log(msg: str) -> None:
    print(f"[{dt.datetime.now(dt.timezone.utc).strftime('%H:%M:%S')}] {msg}", flush=True)


def deep_merge(base: dict, override: dict) -> dict:
    out = dict(base)
    for k, v in (override or {}).items():
        if isinstance(v, dict) and isinstance(out.get(k), dict):
            out[k] = deep_merge(out[k], v)
        else:
            out[k] = v
    return out


def load_config(path: Path | None) -> dict:
    cfg = _load_config_file(path)
    # Permite ajustar el User-Agent desde GitHub Secrets sin tocar el repo.
    ua = os.environ.get("TVTV_USER_AGENT", "").strip()
    if ua:
        cfg["source"]["user_agent"] = ua
    return cfg


def _load_config_file(path: Path | None) -> dict:
    cfg = DEFAULT_CONFIG
    if path and path.exists():
        text = path.read_text(encoding="utf-8")
        try:
            import yaml  # type: ignore
        except ImportError:
            # Fallback: permite config.json si no hay PyYAML en el runner.
            try:
                return deep_merge(cfg, json.loads(text))
            except json.JSONDecodeError as exc:  # pragma: no cover
                raise SystemExit(
                    f"No pude leer {path}: falta PyYAML y no es JSON valido ({exc})"
                )
        return deep_merge(cfg, yaml.safe_load(text) or {})
    return cfg


# --------------------------------------------------------------------------- #
# Cliente HTTP
# --------------------------------------------------------------------------- #

class Source:
    """Cliente minimo para los endpoints htmx de TVTV.us."""

    def __init__(self, cfg: dict) -> None:
        src = cfg["source"]
        self.base = src["base_url"].rstrip("/")
        self.lineup_path = src["lineup_path"]
        self.lineup_id = src["lineup_id"]
        self.ua = src["user_agent"]
        self.timeout = cfg["fetch"]["timeout"]
        self.retries = cfg["fetch"]["retries"]
        self.referer_channel = f"{self.base}{self.lineup_path}"
        self.stats = {"requests": 0, "errors": 0, "retries": 0}

    def _headers(self, partial: bool) -> dict[str, str]:
        h = {"User-Agent": self.ua, "Referer": self.referer_channel, **HEADERS_EXTRA}
        if partial:
            h["hx-request"] = "true"
        return h

    def get(self, path: str, partial: bool = True, retries: int | None = None) -> str:
        url = path if path.startswith("http") else f"{self.base}{path}"
        last_error: Exception | None = None
        attempts = self.retries if retries is None else max(1, retries)
        for attempt in range(attempts):
            try:
                req = urllib.request.Request(url, headers=self._headers(partial))
                with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                    self.stats["requests"] += 1
                    raw = resp.read()
                    return raw.decode("utf-8", "replace")
            except urllib.error.HTTPError as exc:
                last_error = exc
                self.stats["errors"] += 1
                if exc.code in (403, 429, 503):
                    # Cloudflare / rate limit: espera progresiva antes de reintentar.
                    wait = (2 ** attempt) + random.uniform(0, 1.5)
                    log(f"  HTTP {exc.code} en {path} -> reintento en {wait:.1f}s")
                    time.sleep(wait)
                    self.stats["retries"] += 1
                    continue
                raise
            except (urllib.error.URLError, TimeoutError, OSError) as exc:
                last_error = exc
                self.stats["errors"] += 1
                wait = (2 ** attempt) + random.uniform(0, 1.0)
                log(f"  error de red en {path} -> reintento en {wait:.1f}s ({exc})")
                time.sleep(wait)
                self.stats["retries"] += 1
        # Se propaga el HTTPError tal cual (el llamador decide, p. ej. cuota agotada).
        if isinstance(last_error, urllib.error.HTTPError):
            raise last_error
        raise RuntimeError(f"Fallo al pedir {url}: {last_error}")


# --------------------------------------------------------------------------- #
# Parseo de la fuente
# --------------------------------------------------------------------------- #

RE_LINK = re.compile(
    r'<a\b[^>]*data-id="(?P<sid>\d+)"[^>]*data-ch="(?P<ch>[^"]+)"[^>]*href="(?P<href>[^"]+)"',
    re.S,
)
RE_IMG_TITLE = re.compile(r'<img\b[^>]*\btitle="(?P<title>[^"]*)"', re.S)
RE_IMG_ALT = re.compile(r'<img\b[^>]*\balt="(?P<alt>[^"]*)"', re.S)
RE_IMG_LIGHT = re.compile(r'\bdata-light="(?P<logo>[^"]+)"', re.S)
RE_TEXT = re.compile(r'<div>(?P<text>[^<]*)</div>')


def clean_text(raw: str) -> str:
    txt = re.sub(r"<[^>]+>", " ", raw)
    txt = html_mod.unescape(txt)
    txt = re.sub(r"\s+", " ", txt).strip()
    return txt


def slugify(value: str) -> str:
    value = unicodedata.normalize("NFKD", value)
    value = value.encode("ascii", "ignore").decode("ascii")
    value = re.sub(r"[^a-zA-Z0-9]+", "-", value).strip("-").lower()
    return value or "canal"


def parse_channels(page: str, cfg: dict) -> list[dict[str, Any]]:
    """Extrae canales del partial de lineup."""
    src = cfg["source"]
    out: list[dict[str, Any]] = []
    for m in RE_LINK.finditer(page):
        sid, ch, href = m.group("sid"), m.group("ch"), m.group("href")
        # El bloque del ancla termina antes del siguiente <a
        nxt = page.find("<a ", m.end())
        block = page[m.end(): nxt if nxt != -1 else m.end() + 900]
        title = RE_IMG_TITLE.search(block)
        alt = RE_IMG_ALT.search(block)
        light = RE_IMG_LIGHT.search(block)
        text = RE_TEXT.search(block)

        name = (title.group("title") if title else "").strip()
        if not name and alt:
            name = re.sub(r"^\s*\S+\s+", "", alt.group("alt")).strip()  # quita "2 "
        if not name and text:
            name = clean_text(text.group("text"))
        if not name:
            name = clean_text(href.rsplit("-", 1)[-1])
        callsign = clean_text(href.rsplit("-", 1)[-1]) or slugify(name)

        logo = ""
        if light:
            file_name = light.group("logo").split("/")[-1]
            if file_name and file_name != "default":
                logo = f"{src['base_url']}/api/v2/gn/pi/assets/{file_name}"

        out.append(
            {
                "station_id": sid,
                "number": str(ch).strip(),
                "callsign": callsign,
                "name": name,
                "logo": logo,
                "href": href,
            }
        )
    # Dedupe: una estacion puede aparecer en varios numeros de canal.
    # El XMLTV mapea 1 id -> 1 canal, asi que se conserva el primer numero
    # (el mas bajo) y se anotan los numeros alternativos.
    unique = []
    by_station: dict[str, dict[str, Any]] = {}
    for c in out:
        prev = by_station.get(c["station_id"])
        if prev is not None:
            prev.setdefault("alt_numbers", []).append(c["number"])
            continue
        c["alt_numbers"] = []
        by_station[c["station_id"]] = c
        unique.append(c)
    dups = sum(1 for c in unique if c["alt_numbers"])
    if dups:
        log(f"estaciones en varios numeros de canal: {dups} (se usa el primero)")
    return unique


RE_AIRING = re.compile(
    r'<div class="gridAiring(?P<cls>[^"]*)"\s+'
    r'data-id="(?P<pid>[^"]+)"\s+'
    r'data-time="(?P<time>\d+)"\s+'
    r'data-runtime="(?P<runtime>\d+)"'
    r'(?:\s+data-qualifiers="(?P<qual>[^"]*)")?'
    r'[^>]*>(?P<title>.*?)</div>',
    re.S,
)


def parse_airings(page: str) -> list[dict[str, Any]]:
    """Extrae los airings de /partial/source/{ts}/{station}."""
    out = []
    for m in RE_AIRING.finditer(page):
        cls = m.group("cls") or ""
        quals = [q.strip() for q in (m.group("qual") or "").split(",") if q.strip()]
        for token in cls.split():
            if token in ("New", "Live", "R", "CC") and token not in quals:
                quals.append(token)
        title = clean_text(m.group("title"))
        if not title:
            title = "(sin titulo)"
        out.append(
            {
                "programme_id": m.group("pid"),
                "start_ms": int(m.group("time")),
                "runtime": int(m.group("runtime")),  # 0 = desconocido, se resuelve al renderizar
                "title": title,
                "qualifiers": quals,
            }
        )
    return out


RE_H1 = re.compile(r"<h1>(?P<t>.*?)</h1>", re.S)
RE_POSTER = re.compile(r'src="(?P<u>/api/v2/gn/pi/assets/[^"]+)"')
RE_SPAN = re.compile(r"<span>(?P<t>[^<]{2,60})</span>")
RE_P = re.compile(r"<p(?:\s[^>]*)?>(?P<t>.*?)</p>", re.S)


def parse_detail(page: str, base_url: str) -> dict[str, Any]:
    """Extrae genero, sinopsis y poster del dialogo de programa."""
    detail: dict[str, Any] = {}
    h1 = RE_H1.search(page)
    if h1:
        detail["title"] = clean_text(h1.group("t"))

    poster = RE_POSTER.search(page)
    if poster:
        detail["icon"] = f"{base_url}{poster.group('u')}"

    main = page
    start = page.find('id="main-panel"')
    if start != -1:
        end = page.find('id="series-panel"', start)
        main = page[start: end if end != -1 else len(page)]

    genres = [clean_text(g.group("t")) for g in RE_SPAN.finditer(main)]
    genres = [g for g in genres if g and not g.lower().startswith("http")]
    if genres:
        detail["category"] = genres[0]
        if len(genres) > 1:
            detail["categories"] = genres[:3]

    paras = [clean_text(p.group("t")) for p in RE_P.finditer(main)]
    paras = [p for p in paras if len(p) > 40]  # la sinopsis es el parrafo largo
    if paras:
        detail["desc"] = max(paras, key=len)
    return detail


# --------------------------------------------------------------------------- #
# Cache de fichas de programa
# --------------------------------------------------------------------------- #

class DetailCache:
    def __init__(self, path: Path, enabled: bool = True) -> None:
        self.path = path
        self.enabled = enabled
        self.data: dict[str, Any] = {}
        self.dirty = False
        if path.exists():
            try:
                self.data = json.loads(path.read_text(encoding="utf-8"))
            except json.JSONDecodeError:
                log(f"cache corrupta en {path}, se ignora")
                self.data = {}

    def get(self, key: str) -> dict[str, Any] | None:
        return self.data.get(key)

    def put(self, key: str, value: dict[str, Any]) -> None:
        self.data[key] = value
        self.dirty = True

    def save(self) -> None:
        if not self.enabled or not self.dirty:
            return
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(
            json.dumps(self.data, ensure_ascii=False, indent=0, sort_keys=True),
            encoding="utf-8",
        )
        log(f"cache de fichas: {len(self.data)} programas en {self.path}")


# --------------------------------------------------------------------------- #
# Recoleccion
# --------------------------------------------------------------------------- #

def day_timestamps(cfg: dict) -> list[int]:
    """TVTV espera la medianoche UTC del dia calendario UTC, en milisegundos."""
    fetch = cfg["fetch"]
    today = dt.datetime.now(dt.timezone.utc).replace(hour=0, minute=0, second=0, microsecond=0)
    days = []
    for offset in range(-fetch["days_back"], fetch["days_forward"] + 1):
        ts = today + dt.timedelta(days=offset)
        days.append(int(ts.timestamp() * 1000))
    return days


def collect_airings(
    src: Source, channels: list[dict[str, Any]], cfg: dict
) -> dict[str, dict[int, dict[str, Any]]]:
    """Devuelve {station_id: {start_ms: airing}} deduplicado entre dias."""
    stamps = day_timestamps(cfg)
    workers = max(1, int(cfg["fetch"]["workers"]))
    delay = float(cfg["fetch"]["delay_between_days"])
    tasks = [(c["station_id"], ts) for ts in stamps for c in channels]
    by_channel: dict[str, dict[int, dict[str, Any]]] = {c["station_id"]: {} for c in channels}
    done = 0
    failed: list[tuple[str, int]] = []

    def work(job: tuple[str, int]) -> tuple[str, int, str | None]:
        sid, ts = job
        try:
            page = src.get(f"/partial/source/{ts}/{sid}")
            if delay:
                time.sleep(delay / workers)
            return sid, ts, page
        except Exception as exc:  # noqa: BLE001
            log(f"  fallo canal {sid} dia {ts}: {exc}")
            return sid, ts, None

    total = len(tasks)
    log(f"pidiendo {total} paginas ({len(channels)} canales x {len(stamps)} dias, {workers} hilos)")
    with futures.ThreadPoolExecutor(max_workers=workers) as pool:
        for sid, ts, page in pool.map(work, tasks):
            done += 1
            if page is None:
                failed.append((sid, ts))
            else:
                for air in parse_airings(page):
                    by_channel.setdefault(sid, {}).setdefault(air["start_ms"], air)
            if done % 250 == 0 or done == total:
                log(f"  {done}/{total} paginas")
    if failed:
        ratio = len(failed) / total
        log(f"AVISO: {len(failed)} paginas fallaron ({ratio:.1%})")
    return by_channel


def enrich(
    src: Source,
    channels: list[dict[str, Any]],
    by_channel: dict[str, dict[int, dict[str, Any]]],
    cfg: dict,
    cache: DetailCache,
    cooldown_path: Path,
) -> None:
    """
    Añade genero/sinopsis/poster usando /dlg/program.

    Ese endpoint tiene una cuota estricta por IP (HTTP 429). Por eso:
      - se pide de a uno, con pausa entre requests,
      - se respeta un presupuesto por corrida (details_budget),
      - si aparece un 429 se guarda un cooldown y se corta el enriquecimiento,
      - todo lo obtenido queda en cache, asi cada corrida completa un poco mas.
    """
    mode = cfg["fetch"]["details"]
    if mode is False or mode == "off":
        return
    if mode == "cached-only":
        log(f"fichas: solo cache ({len(cache.data)} programas)")
        return

    if cooldown_path.exists():
        try:
            until = float(cooldown_path.read_text().strip() or 0)
        except ValueError:
            until = 0.0
        if time.time() < until:
            mins = (until - time.time()) / 60
            log(f"fichas en pausa por cuota de la fuente ({mins:.0f} min restantes); se usa la cache")
            return

    # Un solo request por id de programa; se cachea por id.
    pending: dict[str, tuple[str, int]] = {}
    for c in channels:
        for start, air in by_channel.get(c["station_id"], {}).items():
            pid = air["programme_id"]
            if pid not in cache.data and pid not in pending:
                pending[pid] = (pid, start)

    budget = int(cfg["fetch"].get("details_budget") or 0)
    queue = list(pending.values())
    if budget > 0:
        queue = queue[:budget]

    log(f"fichas: {len(cache.data)} en cache, {len(pending)} sin datos, se piden {len(queue)}")
    if not queue:
        return

    interval = float(cfg["fetch"].get("details_interval", 1.0))
    got = 0
    for idx, (pid, start) in enumerate(queue, 1):
        try:
            page = src.get(f"/dlg/program?id={pid}&time={start}&", retries=1)
            cache.put(pid, parse_detail(page, cfg["source"]["base_url"]))
            got += 1
        except urllib.error.HTTPError as exc:
            if exc.code in (429, 403):
                cooldown = float(cfg["fetch"].get("details_cooldown_hours", 6)) * 3600
                cooldown_path.parent.mkdir(parents=True, exist_ok=True)
                cooldown_path.write_text(str(time.time() + cooldown))
                log(
                    f"cuota agotada (HTTP {exc.code}); se cortan las fichas "
                    f"y se reintenta en {cooldown / 3600:.0f}h. Obtenidas {got} en esta corrida."
                )
                break
            log(f"  fallo ficha {pid}: {exc}")
        except Exception as exc:  # noqa: BLE001
            log(f"  fallo ficha {pid}: {exc}")
        if idx % 25 == 0:
            log(f"  {idx}/{len(queue)} fichas")
        time.sleep(interval)
    cache.save()
    if got:
        # Cuota recuperada: borra el cooldown si existia
        if cooldown_path.exists() and got >= len(queue):
            cooldown_path.unlink(missing_ok=True)
        log(f"fichas nuevas: {got} (total en cache: {len(cache.data)})")


# --------------------------------------------------------------------------- #
# XMLTV
# --------------------------------------------------------------------------- #

def fmt_xmltv(ms: int) -> str:
    stamp = dt.datetime.fromtimestamp(ms / 1000, tz=dt.timezone.utc)
    return stamp.strftime("%Y%m%d%H%M%S +0000")


def build_ids(channels: list[dict[str, Any]], cfg: dict) -> dict[str, str]:
    prefix = cfg["output"]["id_prefix"]
    overrides = {str(k).upper(): str(v) for k, v in (cfg.get("channel_id_overrides") or {}).items()}
    ids: dict[str, str] = {}
    used: set[str] = set()
    alias: dict[str, str] = {}
    for c in channels:
        override = overrides.get(str(c["callsign"]).upper())
        base = override or f"{prefix}-{slugify(c['number'])}-{slugify(c['callsign'])}"
        cand, n = base, 2
        while cand in used:
            cand = f"{base}-{n}"
            n += 1
        used.add(cand)
        ids[c["station_id"]] = cand
        # alias para clientes que casan por call sign
        if str(c["callsign"]).upper() not in alias:
            alias[str(c["callsign"]).upper()] = cand
    return ids


def filter_channels(channels: list[dict[str, Any]], cfg: dict) -> list[dict[str, Any]]:
    patterns = [re.compile(p, re.I) for p in cfg["output"].get("exclude_channel_patterns", [])]
    if not patterns:
        return channels
    kept = [
        c
        for c in channels
        if not any(p.search(c["number"]) or p.search(c["callsign"]) for p in patterns)
    ]
    if len(kept) != len(channels):
        log(f"canales excluidos por patron: {len(channels) - len(kept)}")
    return kept


def render_xmltv(
    channels: list[dict[str, Any]],
    by_channel: dict[str, dict[int, dict[str, Any]]],
    ids: dict[str, str],
    cache: DetailCache,
    cfg: dict,
) -> tuple[str, dict[str, Any]]:
    out_cfg = cfg["output"]
    lang = cfg["source"]["language"]
    tpl = out_cfg.get("channel_name_template", "{number} {name}")
    show_icons = out_cfg.get("include_icons", True)
    lines: list[str] = []
    stats = {"programmes": 0, "channels": 0, "empty_channels": 0}

    lines.append('<?xml version="1.0" encoding="UTF-8"?>')
    lines.append('<!DOCTYPE tv SYSTEM "xmltv.dtd">')
    lines.append(
        f'<tv generator-info-name={quoteattr(out_cfg["generator"])} '
        f'source-info-name="TVTV.us" source-info-url="https://www.tvtv.us">'
    )

    # --- canales ---------------------------------------------------------- #
    # Cada estacion se publica como un canal principal; si la fuente la lista
    # tambien en otros numeros, se agregan ids alternos que comparten programacion.
    def channel_block(cid: str, c: dict[str, Any], number: str) -> None:
        display = tpl.format(number=number, name=c["name"], callsign=c["callsign"])
        lines.append(f'  <channel id={quoteattr(cid)}>')
        lines.append(f"    <display-name>{escape(display)}</display-name>")
        if c["callsign"] and c["callsign"] != c["name"]:
            lines.append(f'    <display-name>{escape(c["callsign"])}</display-name>')
        if show_icons and c.get("logo"):
            lines.append(f"    <icon src={quoteattr(c['logo'])}/>")
        lines.append("  </channel>")
        stats["channels"] += 1

    for c in channels:
        channel_block(ids[c["station_id"]], c, c["number"])
        for alt in c.get("alt_numbers", []):
            channel_block(f'{ids[c["station_id"]]}-alt{slugify(alt)}', c, alt)

    # --- programacion ----------------------------------------------------- #
    def programme_block(cid: str, c: dict[str, Any]) -> None:
        airings = by_channel.get(c["station_id"], {})
        if not airings:
            stats["empty_channels"] += 1
            return
        starts = sorted(airings)

        # Duracion desconocida (runtime 0): se deduce del siguiente programa.
        resolved: dict[int, int] = {}
        for idx, start in enumerate(starts):
            rt = airings[start]["runtime"]
            if rt <= 0:
                if idx + 1 < len(starts):
                    rt = max(5, min(240, round((starts[idx + 1] - start) / 60_000)))
                else:
                    rt = 30
            resolved[start] = rt

        for idx, start in enumerate(starts):
            air = airings[start]
            stop = start + resolved[start] * 60_000
            if idx + 1 < len(starts):
                stop = min(stop, starts[idx + 1])  # sin solapamientos

            if idx > 0:
                prev = airings[starts[idx - 1]]
                same_end = prev["start_ms"] + resolved[starts[idx - 1]] * 60_000
                if prev["programme_id"] == air["programme_id"] and same_end == start:
                    continue  # la fuente repite el mismo episodio en bloques seguidos

            detail = cache.get(air["programme_id"]) or {}
            lines.append(
                f'  <programme start="{fmt_xmltv(start)}" stop="{fmt_xmltv(stop)}" '
                f'channel={quoteattr(cid)}>'
            )
            title = air["title"]
            if detail.get("title") and len(detail["title"]) > len(title):
                title = detail["title"]
            lines.append(f'    <title lang="{lang}">{escape(title)}</title>')

            categories = detail.get("categories") or (
                [detail["category"]] if detail.get("category") else []
            )
            for cat in categories:
                lines.append(f'    <category lang="{lang}">{escape(cat)}</category>')
            if detail.get("desc"):
                lines.append(f'    <desc lang="{lang}">{escape(detail["desc"])}</desc>')
            if detail.get("icon") and show_icons:
                lines.append(f'    <icon src={quoteattr(detail["icon"])}/>')

            quals = {q.lower() for q in air.get("qualifiers", [])}
            if "new" in quals:
                lines.append("    <new/>")
            if "live" in quals:
                lines.append("    <live/>")
            if "r" in quals:
                lines.append("    <previously-shown/>")
            if "cc" in quals:
                lines.append("    <sub-titles/>")
            lines.append("  </programme>")
            stats["programmes"] += 1

    stats["empty_channels"] = 0
    for c in channels:
        programme_block(ids[c["station_id"]], c)
        for alt in c.get("alt_numbers", []):
            programme_block(f'{ids[c["station_id"]]}-alt{slugify(alt)}', c)

    lines.append("</tv>")
    return "\n".join(lines) + "\n", stats


def validate(stats: dict[str, Any], cfg: dict, strict: bool) -> bool:
    val = cfg["validation"]
    ok = True
    problems = []
    if stats["channels"] < val["min_channels"]:
        problems.append(
            f"canales {stats['channels']} < minimo {val['min_channels']}"
        )
    if stats["programmes"] < val["min_programmes"]:
        problems.append(
            f"programas {stats['programmes']} < minimo {val['min_programmes']}"
        )
    ratio = stats["empty_channels"] / max(1, stats["channels"])
    if ratio > val["max_empty_channel_ratio"]:
        problems.append(
            f"{ratio:.0%} de canales sin programacion (max {val['max_empty_channel_ratio']:.0%})"
        )
    if problems:
        ok = False
        for p in problems:
            log(f"VALIDACION: {p}")
        if strict:
            log("modo estricto: NO se publica el XML")
    return ok


# --------------------------------------------------------------------------- #
# Main
# --------------------------------------------------------------------------- #

def main(argv: Iterable[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Genera XMLTV desde TVTV.us")
    ap.add_argument("--config", type=Path, default=Path("config.yml"))
    ap.add_argument("--out", type=str, default=None, help="archivo de salida (sobreescribe config)")
    ap.add_argument("--cache", type=Path, default=Path("data/detail-cache.json"))
    ap.add_argument("--days-back", type=int, default=None)
    ap.add_argument("--days-forward", type=int, default=None)
    ap.add_argument("--workers", type=int, default=None)
    ap.add_argument("--limit", type=int, default=None, help="limite de canales (pruebas)")
    ap.add_argument("--no-details", action="store_true", help="no pide fichas (usa la cache si existe)")
    ap.add_argument("--details", action="store_true", help="fuerza el enriquecimiento aunque el cooldown siga activo")
    ap.add_argument("--budget", type=int, default=None, help="maximo de fichas nuevas en esta corrida")
    ap.add_argument("--gzip", action="store_true")
    ap.add_argument("--strict", action="store_true", help="sale con codigo 1 si la validacion falla")
    args = ap.parse_args(argv)

    cfg = load_config(args.config)
    if args.out:
        cfg["output"]["file"] = args.out
    if args.days_back is not None:
        cfg["fetch"]["days_back"] = args.days_back
    if args.days_forward is not None:
        cfg["fetch"]["days_forward"] = args.days_forward
    if args.workers is not None:
        cfg["fetch"]["workers"] = args.workers
    if args.no_details:
        cfg["fetch"]["details"] = "cached-only"
    if args.budget is not None:
        cfg["fetch"]["details_budget"] = args.budget

    src = Source(cfg)
    started = time.time()

    log(f"lineup: {cfg['source']['lineup_id']}")
    page = src.get(f"/partial/lineup/{cfg['source']['lineup_id']}")
    channels = filter_channels(parse_channels(page, cfg), cfg)
    if not channels:
        log("ERROR: no se pudo leer ningun canal del lineup")
        return 1
    log(f"canales: {len(channels)}")
    if args.limit:
        channels = channels[: args.limit]
        log(f"limitado a {len(channels)} canales (prueba)")

    by_channel = collect_airings(src, channels, cfg)
    total_airings = sum(len(v) for v in by_channel.values())
    log(f"airings unicos: {total_airings}")

    cache = DetailCache(args.cache, enabled=bool(cfg["fetch"]["details"]))
    cooldown = args.cache.parent / "details-cooldown.txt"
    if args.details:
        cooldown.unlink(missing_ok=True)
    enrich(src, channels, by_channel, cfg, cache, cooldown)

    ids = build_ids(channels, cfg)
    xml, stats = render_xmltv(channels, by_channel, ids, cache, cfg)

    out_path = Path(cfg["output"]["file"])
    out_path.parent.mkdir(parents=True, exist_ok=True)
    if args.gzip:
        out_path = out_path.with_suffix(out_path.suffix + ".gz")
        with gzip.open(out_path, "wt", encoding="utf-8") as fh:
            fh.write(xml)
    else:
        out_path.write_text(xml, encoding="utf-8")

    elapsed = time.time() - started
    size_mb = out_path.stat().st_size / 1_048_576
    log(
        f"listo: {out_path} | {stats['channels']} canales, {stats['programmes']} programas, "
        f"{size_mb:.2f} MB, {elapsed:.0f}s | requests={src.stats['requests']} "
        f"errores={src.stats['errors']} reintentos={src.stats['retries']}"
    )
    ok = validate(stats, cfg, args.strict)
    if not ok and args.strict:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
