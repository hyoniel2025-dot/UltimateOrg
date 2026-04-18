#!/usr/bin/env python3
"""
Telegram Bot v3.1 — Archivador en la Nube
Pyrogram + MTProto | Archivos hasta 2 GB
"""

import os
import asyncio
import logging
import shutil
import re
import json
import subprocess
import mimetypes
import time
import uuid
from pathlib import Path
from urllib.parse import urlparse, unquote
from datetime import date
import threading
from http.server import HTTPServer, BaseHTTPRequestHandler

# ─── Compatibilidad Python 3.10+ / 3.14 (Pyrogram requiere event loop al importar) ──
try:
    _loop = asyncio.get_event_loop()
    if _loop.is_closed():
        raise RuntimeError("closed")
except RuntimeError:
    asyncio.set_event_loop(asyncio.new_event_loop())

from dotenv import load_dotenv
load_dotenv()

import aiohttp
import aiofiles
import aiosqlite
import internetarchive as ia

try:
    import py7zr
    _PY7ZR_AVAILABLE = True
except ImportError:
    _PY7ZR_AVAILABLE = False

from pyrogram import Client, filters, idle, enums
from pyrogram.types import (
    Message,
    InlineKeyboardMarkup,
    InlineKeyboardButton,
    CallbackQuery,
    BotCommand,
    BotCommandScopeDefault,
    BotCommandScopeChat,
)

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger(__name__)

# ─── Configuración ─────────────────────────────────────────────────────────────

def _safe_int(value: str, default: int = 0) -> int:
    try:
        return int(str(value).strip())
    except (ValueError, TypeError):
        return default


BOT_TOKEN          = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
API_ID             = _safe_int(os.environ.get("TELEGRAM_API_ID", "0"))
API_HASH           = os.environ.get("TELEGRAM_API_HASH", "").strip()
_ADMIN_RAW         = os.environ.get("TELEGRAM_ADMIN_ID", "").strip().lstrip("@")
_raw_contact = os.environ.get("TELEGRAM_ADMIN_USERNAME", "").strip()
if _raw_contact.startswith("https://t.me/"):
    _raw_contact = _raw_contact[len("https://t.me/"):]
elif _raw_contact.startswith("t.me/"):
    _raw_contact = _raw_contact[len("t.me/"):]
_ADMIN_CONTACT_RAW = _raw_contact.lstrip("@")
ARCHIVE_ACCESS     = os.environ.get("ARCHIVE_ORG_ACCESS_KEY", "").strip()
ARCHIVE_SECRET     = os.environ.get("ARCHIVE_ORG_SECRET_KEY", "").strip()

_ADMIN_ID: int | None = None
_ADMIN_USERNAME: str | None = None
if _ADMIN_RAW.lstrip("-").isdigit():
    _ADMIN_ID = int(_ADMIN_RAW)
elif _ADMIN_RAW:
    _ADMIN_USERNAME = _ADMIN_RAW.lower()

USERS_FILE    = Path("users.json")
DB_FILE       = Path("bot_data.db")
TEMP_DIR      = Path("temp_downloads")
TEMP_DIR.mkdir(exist_ok=True)
HEALTH_PORT   = _safe_int(os.environ.get("PORT", "8080"), 8080)

DEFAULT_QUOTA = 10
PM = enums.ParseMode.HTML

# ─── Estado global ─────────────────────────────────────────────────────────────

job_queues:       dict[int, asyncio.Queue] = {}
active_tasks:     dict[int, dict]          = {}
pending_quality:  dict[str, dict]          = {}
pending_playlist: dict[str, dict]          = {}

# ─── Contacto admin ────────────────────────────────────────────────────────────

def admin_contact_url() -> str:
    if _ADMIN_CONTACT_RAW:
        return f"https://t.me/{_ADMIN_CONTACT_RAW}"
    if _ADMIN_USERNAME:
        return f"https://t.me/{_ADMIN_USERNAME}"
    return "https://t.me"


def admin_contact_btn() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("📩 Contactar Administrador", url=admin_contact_url())
    ]])

# ─── Utilidades de texto ───────────────────────────────────────────────────────

def bi(text: str) -> str:
    result = []
    for ch in text:
        if "A" <= ch <= "Z":
            result.append(chr(0x1D63C + ord(ch) - ord("A")))
        elif "a" <= ch <= "z":
            result.append(chr(0x1D656 + ord(ch) - ord("a")))
        elif "0" <= ch <= "9":
            result.append(chr(0x1D7EC + ord(ch) - ord("0")))
        else:
            result.append(ch)
    return "".join(result)


def esc(text: str) -> str:
    return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def fmt_size(size_bytes: int) -> str:
    if size_bytes < 1024:
        return f"{size_bytes} B"
    elif size_bytes < 1024 ** 2:
        return f"{size_bytes / 1024:.1f} KB"
    elif size_bytes < 1024 ** 3:
        return f"{size_bytes / 1024 ** 2:.1f} MB"
    else:
        return f"{size_bytes / 1024 ** 3:.2f} GB"


def fmt_eta(seconds: float) -> str:
    if seconds < 0 or seconds > 86400:
        return "—"
    elif seconds < 60:
        return f"{int(seconds)}s"
    elif seconds < 3600:
        return f"{int(seconds // 60)}m {int(seconds % 60)}s"
    else:
        return f"{int(seconds // 3600)}h {int((seconds % 3600) // 60)}m"


def progress_bar(pct: float, width: int = 18) -> str:
    filled = int(width * pct / 100)
    return "█" * filled + "░" * (width - filled)


def sanitize_name(name: str) -> str:
    name = re.sub(r"[^\w\s\-.]", "", name)
    name = name.strip().replace(" ", "_")
    return name[:80] if name else "archivo"


# ─── Gestión de usuarios ───────────────────────────────────────────────────────

def _admin_matches(uid: int, uname: str | None) -> bool:
    if _ADMIN_ID is not None and uid == _ADMIN_ID:
        return True
    if _ADMIN_USERNAME and uname and uname.lower() == _ADMIN_USERNAME:
        return True
    return False


def load_users() -> dict:
    if USERS_FILE.exists():
        try:
            with open(USERS_FILE, "r") as f:
                data = json.load(f)
            data.setdefault("allowed", [])
            data.setdefault("banned", [])
            return data
        except Exception:
            pass
    initial: list = []
    if _ADMIN_ID:
        initial.append(_ADMIN_ID)
    if _ADMIN_USERNAME:
        initial.append(_ADMIN_USERNAME)
    return {"allowed": initial, "banned": []}


def save_users(data: dict):
    with open(USERS_FILE, "w") as f:
        json.dump(data, f, indent=2)


def _in_list(lst: list, uid: int, uname: str | None) -> bool:
    if uid in lst:
        return True
    if uname and uname.lower() in [str(x).lower() for x in lst]:
        return True
    return False


def is_admin(uid: int, uname: str | None = None) -> bool:
    return _admin_matches(uid, uname)


def is_allowed(uid: int, uname: str | None = None) -> bool:
    if _admin_matches(uid, uname):
        return True
    data = load_users()
    return _in_list(data["allowed"], uid, uname) and not _in_list(data["banned"], uid, uname)


def is_banned(uid: int, uname: str | None = None) -> bool:
    return _in_list(load_users()["banned"], uid, uname)


# ─── Base de datos ─────────────────────────────────────────────────────────────

async def init_db():
    async with aiosqlite.connect(DB_FILE) as db:
        await db.execute("""
            CREATE TABLE IF NOT EXISTS upload_history (
                id         INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id    INTEGER NOT NULL,
                username   TEXT,
                first_name TEXT,
                filename   TEXT,
                link       TEXT,
                size       INTEGER DEFAULT 0,
                created_at TEXT DEFAULT (datetime('now', 'localtime'))
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS daily_usage (
                user_id INTEGER,
                date    TEXT,
                count   INTEGER DEFAULT 0,
                PRIMARY KEY (user_id, date)
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS user_quota (
                user_id     INTEGER PRIMARY KEY,
                daily_limit INTEGER DEFAULT 10
            )
        """)
        await db.commit()


async def get_daily_usage(uid: int) -> int:
    today = date.today().isoformat()
    async with aiosqlite.connect(DB_FILE) as db:
        async with db.execute(
            "SELECT count FROM daily_usage WHERE user_id=? AND date=?", (uid, today)
        ) as cur:
            row = await cur.fetchone()
            return row[0] if row else 0


async def get_quota(uid: int) -> int:
    async with aiosqlite.connect(DB_FILE) as db:
        async with db.execute(
            "SELECT daily_limit FROM user_quota WHERE user_id=?", (uid,)
        ) as cur:
            row = await cur.fetchone()
            return row[0] if row else DEFAULT_QUOTA


async def set_quota(uid: int, limit: int):
    async with aiosqlite.connect(DB_FILE) as db:
        await db.execute(
            "INSERT INTO user_quota (user_id, daily_limit) VALUES (?, ?) "
            "ON CONFLICT(user_id) DO UPDATE SET daily_limit=?",
            (uid, limit, limit),
        )
        await db.commit()


async def increment_usage(uid: int):
    today = date.today().isoformat()
    async with aiosqlite.connect(DB_FILE) as db:
        await db.execute(
            "INSERT INTO daily_usage (user_id, date, count) VALUES (?, ?, 1) "
            "ON CONFLICT(user_id, date) DO UPDATE SET count = count + 1",
            (uid, today),
        )
        await db.commit()


async def add_history(uid: int, uname: str | None, fname: str, filename: str, link: str, size: int):
    async with aiosqlite.connect(DB_FILE) as db:
        await db.execute(
            "INSERT INTO upload_history (user_id, username, first_name, filename, link, size) "
            "VALUES (?, ?, ?, ?, ?, ?)",
            (uid, uname or "", fname, filename, link, size),
        )
        await db.commit()


async def get_history(uid: int, limit: int = 10) -> list:
    async with aiosqlite.connect(DB_FILE) as db:
        async with db.execute(
            "SELECT filename, link, size, created_at FROM upload_history "
            "WHERE user_id=? ORDER BY id DESC LIMIT ?",
            (uid, limit),
        ) as cur:
            return await cur.fetchall()


# ─── Detección de URLs ─────────────────────────────────────────────────────────

PLATFORM_PATTERNS = [
    r"(?:https?://)?(?:www\.)?youtube\.com/",
    r"(?:https?://)?youtu\.be/",
    r"(?:https?://)?(?:www\.)?instagram\.com/",
    r"(?:https?://)?(?:vm\.)?tiktok\.com/",
    r"(?:https?://)?(?:www\.)?tiktok\.com/",
    r"(?:https?://)?(?:www\.)?twitter\.com/",
    r"(?:https?://)?(?:www\.)?x\.com/",
]


def is_platform_url(url: str) -> bool:
    return any(re.search(p, url, re.IGNORECASE) for p in PLATFORM_PATTERNS)


def is_youtube_playlist(url: str) -> bool:
    return (
        bool(re.search(r"(?:list=|/playlist\?)", url, re.IGNORECASE))
        and bool(re.search(r"youtube\.com|youtu\.be", url, re.IGNORECASE))
    )


def extract_url(text: str) -> str | None:
    matches = re.findall(r"https?://[^\s<>\"{}|\\^`\[\]]+", text, re.IGNORECASE)
    return matches[0] if matches else None


# ─── Barra de progreso ─────────────────────────────────────────────────────────

DIV = "▬" * 18


class ProgressState:
    def __init__(self):
        self.current = 0
        self.total = 0
        self.start_time = time.time()
        self.last_edit = 0.0

    def update(self, current: int, total: int):
        self.current = current
        self.total = total

    def render(self, label: str, emoji: str = "⬇️") -> str:
        elapsed = max(time.time() - self.start_time, 0.001)
        speed = self.current / elapsed if elapsed > 0 else 0
        if self.total > 0:
            pct = min(100.0, self.current / self.total * 100)
            remaining = (self.total - self.current) / speed if speed > 0 else -1
            bar = progress_bar(pct)
            return (
                f"{emoji}  <b>{bi(label)}</b>\n"
                f"<code>{DIV}</code>\n"
                f"<code>{bar}</code>  <b>{bi(f'{pct:.1f}%')}</b>\n\n"
                f"📦  {bi(fmt_size(self.current))} / {bi(fmt_size(self.total))}\n"
                f"⚡  {bi(fmt_size(int(speed)) + '/s')}  ·  ⏱  {bi(fmt_eta(remaining))}"
            )
        else:
            return (
                f"{emoji}  <b>{bi(label)}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"📦  {bi(fmt_size(self.current))} transferidos\n"
                f"⚡  {bi(fmt_size(int(speed)) + '/s')}"
            )


async def safe_edit(app: Client, chat_id: int, msg_id: int, text: str, markup=None):
    try:
        await app.edit_message_text(chat_id, msg_id, text, parse_mode=PM, reply_markup=markup)
    except Exception as e:
        logger.debug(f"safe_edit: {e}")


def cancel_kb(uid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("⏹ Cancelar tarea", callback_data=f"cancel_{uid}")]])


# ─── Descarga MTProto (Pyrogram, hasta 2 GB) ───────────────────────────────────

async def download_telegram_file_mtproto(
    app: Client,
    message: Message,
    dest_path: Path,
    chat_id: int,
    status_msg_id: int,
    cancel_event: asyncio.Event,
) -> bool:
    progress = ProgressState()

    async def progress_cb(current: int, total: int):
        progress.update(current, total)
        now = time.time()
        if now - progress.last_edit >= 3.0:
            progress.last_edit = now
            await safe_edit(
                app, chat_id, status_msg_id,
                progress.render("Descargando archivo", "⬇️"),
                markup=cancel_kb(chat_id),
            )

    try:
        download_task = asyncio.create_task(
            message.download(str(dest_path), progress=progress_cb)
        )
        while not download_task.done():
            if cancel_event.is_set():
                download_task.cancel()
                return False
            await asyncio.sleep(0.5)
        await download_task
        return dest_path.exists()
    except asyncio.CancelledError:
        return False
    except Exception as e:
        logger.error(f"Error descargando MTProto: {e}")
        return False


# ─── Descarga yt-dlp (YouTube · Instagram · TikTok · Twitter/X) ───────────────

QUALITY_MAP: dict[str, list] = {
    "best":  [],
    "1080":  ["-f", "bestvideo[height<=1080]+bestaudio/best[height<=1080]"],
    "720":   ["-f", "bestvideo[height<=720]+bestaudio/best[height<=720]"],
    "480":   ["-f", "bestvideo[height<=480]+bestaudio/best[height<=480]"],
    "360":   ["-f", "bestvideo[height<=360]+bestaudio/best[height<=360]"],
    "audio": ["-f", "bestaudio", "-x", "--audio-format", "mp3"],
}

QUALITY_LABELS = {
    "best":  "⭐ Mejor calidad",
    "1080":  "📺 1080p",
    "720":   "📺 720p",
    "480":   "📺 480p",
    "360":   "📺 360p",
    "audio": "🎵 Solo audio",
}


async def _run_ytdlp_proc(
    cmd: list,
    cancel_event: asyncio.Event,
) -> tuple[int, str]:
    """Ejecuta yt-dlp de forma async con soporte de cancelación. Retorna (returncode, stderr)."""
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        while proc.returncode is None:
            if cancel_event.is_set():
                try:
                    proc.kill()
                except Exception:
                    pass
                await proc.wait()
                return -999, "cancelado"
            try:
                await asyncio.wait_for(proc.wait(), timeout=1.0)
            except asyncio.TimeoutError:
                pass
        stderr_out = b""
        if proc.stderr:
            stderr_out = await proc.stderr.read()
        return proc.returncode, stderr_out.decode(errors="ignore")
    except asyncio.CancelledError:
        return -999, "cancelado"
    except Exception as e:
        return -1, str(e)


async def download_platform(
    url: str,
    dest_dir: Path,
    quality: str,
    chat_id: int,
    status_msg_id: int,
    app: Client,
    cancel_event: asyncio.Event,
    playlist: bool = False,
) -> tuple[list[Path], str]:
    quality_flags = QUALITY_MAP.get(quality, [])
    playlist_flag = [] if playlist else ["--no-playlist"]
    short_url = url[:55] + "…" if len(url) > 55 else url

    await safe_edit(
        app, chat_id, status_msg_id,
        f"🌐  <b>{bi('Analizando enlace...')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"🔗  <code>{esc(short_url)}</code>\n\n"
        f"⏳  {bi('Obteniendo información...')}",
        markup=cancel_kb(chat_id),
    )

    # ── Opciones base siempre presentes ──────────────────────────────────────
    BASE_OPTS = [
        "--no-check-certificate",
        "--geo-bypass",
        "--force-ipv4",
        "--no-warnings",
        "--retries", "10",
        "--fragment-retries", "15",
        "--retry-sleep", "linear=1::3",
        "--concurrent-fragments", "4",
        "--merge-output-format", "mp4",
        "--age-limit", "99",
        "-o", str(dest_dir / "%(title)s.%(ext)s"),
    ]

    # Formato adaptado a la calidad pedida, con múltiples fallbacks
    if quality == "audio":
        fmt_flags = ["-f", "bestaudio", "-x", "--audio-format", "mp3"]
    elif quality == "best":
        fmt_flags = [
            "-f",
            "bestvideo[ext=mp4]+bestaudio[ext=m4a]/"
            "bestvideo+bestaudio/best[ext=mp4]/best",
        ]
    else:
        h = quality  # "1080", "720", "480"
        fmt_flags = [
            "-f",
            f"bestvideo[height<={h}][ext=mp4]+bestaudio[ext=m4a]/"
            f"bestvideo[height<={h}]+bestaudio/"
            f"best[height<={h}][ext=mp4]/"
            f"best[height<={h}]/best",
        ]

    # ── Estrategias de descarga en orden de efectividad ────────────────────
    STRATEGIES = [
        {
            "label": "tv_embedded + ios",
            "extra": [
                "--extractor-args",
                "youtube:player_client=tv_embedded,ios",
            ],
        },
        {
            "label": "ios + android",
            "extra": [
                "--extractor-args",
                "youtube:player_client=ios,android,android_embedded",
            ],
        },
        {
            "label": "web_embedded + mweb",
            "extra": [
                "--extractor-args",
                "youtube:player_client=web_embedded,mweb,web",
                "--add-headers", "Referer:https://www.youtube.com/",
                "--user-agent",
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/124.0.0.0 Safari/537.36",
            ],
        },
        {
            "label": "formato simple",
            "extra": [
                "--extractor-args",
                "youtube:player_client=tv_embedded,ios,web",
                "--format", "best[ext=mp4]/best",
            ],
            "override_fmt": True,
        },
        {
            "label": "modo compatibilidad máxima",
            "extra": [
                "--extractor-args",
                "youtube:player_client=ios,tv_embedded,web,mweb,android",
                "--legacy-server-connect",
                "--format", "worst[ext=mp4]/worst",
                "--ignore-errors",
            ],
            "override_fmt": True,
        },
    ]

    # ── Obtener título ────────────────────────────────────────────────────
    title = "video"
    for client in ["tv_embedded,ios", "ios,android", "web"]:
        if cancel_event.is_set():
            return [], title
        try:
            info_r = await asyncio.get_running_loop().run_in_executor(
                None,
                lambda c=client: subprocess.run(
                    [
                        "yt-dlp", "--get-title", "--no-warnings",
                        "--no-check-certificate", "--geo-bypass",
                        "--extractor-args", f"youtube:player_client={c}",
                    ] + playlist_flag + [url],
                    capture_output=True, text=True, timeout=30,
                ),
            )
            if info_r.returncode == 0 and info_r.stdout.strip():
                title = info_r.stdout.strip().split("\n")[0]
                break
        except Exception:
            pass

    if cancel_event.is_set():
        return [], title

    qlabel = QUALITY_LABELS.get(quality, quality)

    # ── Bucle de intentos ────────────────────────────────────────────────
    for attempt_num, strategy in enumerate(STRATEGIES, 1):
        if cancel_event.is_set():
            return [], title

        # Limpiar archivos parciales entre intentos
        for f in dest_dir.glob("*.part"):
            try:
                f.unlink()
            except Exception:
                pass

        extra   = strategy["extra"]
        label   = strategy["label"]
        use_fmt = [] if strategy.get("override_fmt") else fmt_flags

        await safe_edit(
            app, chat_id, status_msg_id,
            f"⬇️  <b>{bi('Descargando...')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"🎞  <b>{esc(title[:55])}</b>\n"
            f"🔗  <code>{esc(short_url)}</code>\n"
            f"🎚  {bi(qlabel)}\n\n"
            f"🔄  {bi(f'Intento {attempt_num}/{len(STRATEGIES)}: {label}')}\n"
            f"⏳  {bi('Procesando...')}",
            markup=cancel_kb(chat_id),
        )

        cmd = ["yt-dlp"] + BASE_OPTS + extra + use_fmt + playlist_flag + [url]

        rc, stderr_txt = await _run_ytdlp_proc(cmd, cancel_event)

        if rc == -999:
            return [], title

        if rc == 0:
            files = [f for f in sorted(dest_dir.glob("*")) if f.suffix != ".part"]
            if files:
                logger.info(f"yt-dlp éxito en intento {attempt_num} ({label})")
                return files, title

        logger.warning(f"yt-dlp intento {attempt_num} ({label}) falló (rc={rc}): {stderr_txt[:200]}")

    # Todos los intentos fallaron
    logger.error(f"yt-dlp: todos los intentos fallaron para {url}")
    return [], title


# ─── Descarga directa de URL ───────────────────────────────────────────────────

async def download_url_direct(
    url: str,
    dest_dir: Path,
    chat_id: int,
    status_msg_id: int,
    app: Client,
    cancel_event: asyncio.Event,
) -> tuple[Path | None, str]:
    progress = ProgressState()
    headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"}
    short_url = url[:55] + "…" if len(url) > 55 else url

    try:
        conn = aiohttp.TCPConnector(ssl=True)
        async with aiohttp.ClientSession(connector=conn, headers=headers) as session:
            async with session.head(url, allow_redirects=True, timeout=aiohttp.ClientTimeout(total=30)) as r:
                final_url = str(r.url)
            async with session.get(final_url, timeout=aiohttp.ClientTimeout(total=7200)) as resp:
                resp.raise_for_status()
                total = _safe_int(resp.headers.get("Content-Length", "0"))
                progress.total = total

                cd = resp.headers.get("Content-Disposition", "")
                file_name = None
                if "filename=" in cd:
                    m = re.search(r'filename[^;=\n]*=["\']?([^;\n"\']+)', cd)
                    if m:
                        file_name = unquote(m.group(1).strip())
                if not file_name:
                    path_part = unquote(urlparse(final_url).path)
                    file_name = Path(path_part).name or "archivo_descargado"
                if not Path(file_name).suffix:
                    ct = resp.headers.get("Content-Type", "")
                    ext = mimetypes.guess_extension(ct.split(";")[0].strip()) or ".bin"
                    file_name += ext
                file_name = sanitize_name(Path(file_name).stem) + Path(file_name).suffix
                file_path = dest_dir / file_name

                async with aiofiles.open(str(file_path), "wb") as f:
                    async for chunk in resp.content.iter_chunked(512 * 1024):
                        if cancel_event.is_set():
                            return None, ""
                        await f.write(chunk)
                        progress.update(progress.current + len(chunk), total)
                        now = time.time()
                        if now - progress.last_edit >= 3.0:
                            progress.last_edit = now
                            await safe_edit(
                                app, chat_id, status_msg_id,
                                progress.render("Descargando archivo", "⬇️"),
                                markup=cancel_kb(chat_id),
                            )
                return file_path, Path(file_name).stem

    except Exception as e:
        logger.error(f"Error descarga directa: {e}")

    # Fallback yt-dlp
    try:
        await safe_edit(
            app, chat_id, status_msg_id,
            f"🔄  <b>{bi('Método alternativo...')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"🔗  <code>{esc(short_url)}</code>\n\n"
            f"⏳  {bi('Reintentando descarga...')}",
            markup=cancel_kb(chat_id),
        )
        fallback_proc = await asyncio.create_subprocess_exec(
            "yt-dlp", "--no-playlist",
            "--extractor-args",
            "youtube:player_client=ios,web,mweb,android,android_embedded",
            "--no-check-certificate",
            "--force-ipv4",
            "--no-warnings",
            "-o", str(dest_dir / "%(title)s.%(ext)s"),
            url,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        while fallback_proc.returncode is None:
            if cancel_event.is_set():
                try:
                    fallback_proc.kill()
                except Exception:
                    pass
                await fallback_proc.wait()
                return None, ""
            try:
                await asyncio.wait_for(fallback_proc.wait(), timeout=1.0)
            except asyncio.TimeoutError:
                pass
        files = list(dest_dir.glob("*"))
        if files:
            return files[0], files[0].stem
    except Exception as e2:
        logger.error(f"yt-dlp fallback: {e2}")

    return None, "archivo"


# ─── Detección de binario 7z ───────────────────────────────────────────────────

def _find_7z_binary() -> str | None:
    for name in ("7z", "7za", "7zz", "7zzs"):
        if shutil.which(name):
            return name
    return None


# ─── Compresión py7zr (fallback sin binario) ───────────────────────────────────

async def _compress_py7zr(
    file_path: Path,
    archive_path: Path,
    archive_name: str,
    chat_id: int,
    status_msg_id: int,
    app: Client,
) -> Path:
    file_size = file_path.stat().st_size
    await safe_edit(
        app, chat_id, status_msg_id,
        f"🗜  <b>{bi('Comprimiendo...')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"📂  <b>{esc(archive_name[:55])}</b>\n"
        f"📦  {bi(fmt_size(file_size))}\n\n"
        f"⏳  {bi('Procesando (modo py7zr)...')}",
    )

    def _do_compress():
        with py7zr.SevenZipFile(str(archive_path), mode="w") as zf:
            zf.write(str(file_path), file_path.name)

    await asyncio.get_running_loop().run_in_executor(None, _do_compress)

    if not archive_path.exists():
        raise RuntimeError("No se generó el archivo comprimido (py7zr).")

    await safe_edit(
        app, chat_id, status_msg_id,
        f"🗜  <b>{bi('Compresión completa')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"📂  <b>{esc(archive_name[:55])}</b>\n"
        f"📦  {bi(fmt_size(file_size))}\n\n"
        f"<code>{'█' * 18}</code>  <b>{bi('100.0%')}</b>\n\n"
        f"✅  {bi('Listo para subir a la nube...')}",
    )
    return archive_path


# ─── Compresión 7z con barra de progreso en tiempo real ───────────────────────

async def compress_file_with_progress(
    file_path: Path,
    output_dir: Path,
    archive_name: str,
    chat_id: int,
    status_msg_id: int,
    app: Client,
    cancel_event: asyncio.Event | None = None,
) -> Path:
    archive_path = output_dir / f"{archive_name}.7z"

    seven_z = _find_7z_binary()
    if not seven_z:
        if _PY7ZR_AVAILABLE:
            logger.info("Binario 7z no encontrado — usando py7zr como fallback")
            return await _compress_py7zr(file_path, archive_path, archive_name, chat_id, status_msg_id, app)
        raise RuntimeError(
            "7z no está instalado y py7zr no está disponible. "
            "Instala p7zip o py7zr en el servidor."
        )

    cmd = [
        seven_z, "a", "-t7z", "-mx=1", "-mmt=on",
        "-bsp1",
        str(archive_path), str(file_path),
    ]

    file_size = file_path.stat().st_size
    current_pct: list[float] = [0.0]
    last_edit: list[float] = [0.0]

    proc = await asyncio.create_subprocess_exec(
        *cmd,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
    )

    async def read_stdout():
        buf = b""
        while True:
            chunk = await proc.stdout.read(256)
            if not chunk:
                break
            buf += chunk
            matches = re.findall(rb"(\d{1,3})%", buf)
            if matches:
                current_pct[0] = float(matches[-1])
            if len(buf) > 4096:
                buf = buf[-512:]
            now = time.time()
            if now - last_edit[0] >= 2.5:
                last_edit[0] = now
                pct = current_pct[0]
                bar = progress_bar(pct)
                await safe_edit(
                    app, chat_id, status_msg_id,
                    f"🗜  <b>{bi('Comprimiendo...')}</b>\n"
                    f"<code>{DIV}</code>\n\n"
                    f"📂  <b>{esc(archive_name[:55])}</b>\n"
                    f"📦  {bi(fmt_size(file_size))}\n\n"
                    f"<code>{bar}</code>  <b>{bi(f'{pct:.1f}%')}</b>\n\n"
                    f"⚡  {bi('Compresión 7z · modo rápido · archivo único')}",
                    markup=cancel_kb(chat_id),
                )

    progress_task = asyncio.create_task(read_stdout())

    try:
        while proc.returncode is None:
            if cancel_event and cancel_event.is_set():
                try:
                    proc.kill()
                except Exception:
                    pass
                await proc.wait()
                raise asyncio.CancelledError("Cancelado por el usuario")
            try:
                await asyncio.wait_for(proc.wait(), timeout=1.0)
            except asyncio.TimeoutError:
                pass
    finally:
        progress_task.cancel()
        try:
            await progress_task
        except asyncio.CancelledError:
            pass

    if proc.returncode != 0:
        stderr_data = await proc.stderr.read()
        raise RuntimeError(f"Error al comprimir: {stderr_data.decode(errors='ignore')[:300]}")

    if not archive_path.exists():
        raise RuntimeError("No se generó el archivo comprimido.")

    await safe_edit(
        app, chat_id, status_msg_id,
        f"🗜  <b>{bi('Compresión completa')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"📂  <b>{esc(archive_name[:55])}</b>\n"
        f"📦  {bi(fmt_size(file_size))}\n\n"
        f"<code>{'█' * 18}</code>  <b>{bi('100.0%')}</b>\n\n"
        f"✅  {bi('Listo para subir a la nube...')}",
    )

    return archive_path


# ─── Subida a la nube (aiohttp streaming con progreso real) ────────────────────

_UPLOAD_CHUNK = 256 * 1024   # 256 KB por chunk


async def upload_to_cloud(
    archive_path: Path,
    title: str,
    chat_id: int,
    status_msg_id: int,
    app: Client,
    cancel_event: asyncio.Event | None = None,
) -> tuple[str, str]:
    identifier = re.sub(
        r"[^a-zA-Z0-9_-]", "-",
        f"tgbot-{sanitize_name(title)}-{uuid.uuid4().hex[:8]}"
    )[:80]

    total_size   = archive_path.stat().st_size
    uploaded_ref = [0]
    start_time   = time.time()

    await safe_edit(
        app, chat_id, status_msg_id,
        f"☁️  <b>{bi('Subiendo a la nube...')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"📂  <b>{esc(title[:50])}</b>\n"
        f"📦  {bi(fmt_size(total_size))}\n\n"
        f"<code>{'░' * 18}</code>  <b>{bi('0.0%')}</b>\n\n"
        f"⏳  {bi('Iniciando transferencia...')}",
        markup=cancel_kb(chat_id),
    )

    # ── Generador async que lee el archivo por chunks y actualiza el progreso ──
    async def file_sender():
        async with aiofiles.open(str(archive_path), "rb") as f:
            while True:
                if cancel_event and cancel_event.is_set():
                    return
                chunk = await f.read(_UPLOAD_CHUNK)
                if not chunk:
                    break
                uploaded_ref[0] += len(chunk)
                yield chunk

    # ── Tarea que actualiza el mensaje de progreso cada 3 s ──────────────────
    async def progress_updater():
        while True:
            await asyncio.sleep(3)
            ub      = uploaded_ref[0]
            elapsed = max(time.time() - start_time, 0.001)
            speed   = ub / elapsed if elapsed > 0 else 0
            pct     = min(99.0, ub / total_size * 100) if total_size > 0 else 0
            rem     = (total_size - ub) / speed if speed > 0 else -1
            bar     = progress_bar(pct)
            await safe_edit(
                app, chat_id, status_msg_id,
                f"☁️  <b>{bi('Subiendo a la nube...')}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"📂  <b>{esc(title[:50])}</b>\n"
                f"📦  {bi(fmt_size(total_size))}\n\n"
                f"<code>{bar}</code>  <b>{bi(f'{pct:.1f}%')}</b>\n\n"
                f"📤  {bi(fmt_size(ub))} / {bi(fmt_size(total_size))}\n"
                f"⚡  {bi(fmt_size(int(speed)) + '/s')}  ·  ⏱  {bi(fmt_eta(rem))}",
                markup=cancel_kb(chat_id),
            )

    # ── Headers S3 de Archive.org ─────────────────────────────────────────────
    headers = {
        "authorization":             f"LOW {ARCHIVE_ACCESS}:{ARCHIVE_SECRET}",
        "x-archive-auto-make-bucket": "1",
        "x-archive-queue-derive":     "0",
        "x-archive-meta-mediatype":   "data",
        "x-archive-meta-title":       title,
        "x-archive-meta-description": f"Subido por Telegram Bot. Nombre: {title}",
        "x-archive-meta-subject":     "telegram-bot-upload",
        "content-type":               "application/octet-stream",
        "content-length":             str(total_size),
    }
    upload_url = (
        f"https://s3.us.archive.org/{identifier}/"
        f"{archive_path.name}"
    )

    updater_task = asyncio.create_task(progress_updater())
    try:
        connector = aiohttp.TCPConnector(ssl=False, limit=1)
        timeout   = aiohttp.ClientTimeout(total=7200, connect=30)
        async with aiohttp.ClientSession(connector=connector) as session:
            async with session.put(
                upload_url,
                headers=headers,
                data=file_sender(),
                timeout=timeout,
            ) as resp:
                if resp.status not in (200, 201):
                    body = await resp.text()
                    raise RuntimeError(
                        f"Archive.org S3 error {resp.status}: {body[:200]}"
                    )
    finally:
        updater_task.cancel()
        try:
            await updater_task
        except asyncio.CancelledError:
            pass

    link = f"https://archive.org/download/{identifier}/{archive_path.name}"
    return link, identifier


# ─── Resultado como archivo .txt (solo el enlace) ─────────────────────────────

async def send_result_txt(
    app: Client,
    chat_id: int,
    title: str,
    link: str,
    identifier: str,
    archive_size: int,
):
    safe_title = sanitize_name(title)
    txt_name = f"{safe_title}.txt"
    txt_path = TEMP_DIR / txt_name

    async with aiofiles.open(str(txt_path), "w", encoding="utf-8") as f:
        await f.write(link + "\n")

    caption = (
        f"╔══════════════════════════╗\n"
        f"║  ✅  <b>{bi('¡Listo en la Nube!')}</b>  ║\n"
        f"╚══════════════════════════╝\n\n"
        f"🎯  <b>{esc(title[:60])}</b>\n"
        f"📦  {bi(fmt_size(archive_size))}  ·  🗜  7z  ·  {bi('Archivo único')}\n\n"
        f"📄  {bi('El enlace de descarga está en el archivo adjunto')} 👆\n\n"
        f"⏰  <i>Disponible en la nube en unos minutos.</i>"
    )

    await app.send_document(
        chat_id,
        str(txt_path),
        caption=caption,
        parse_mode=PM,
        file_name=txt_name,
    )
    try:
        txt_path.unlink()
    except Exception:
        pass


# ─── Verificar cuota ───────────────────────────────────────────────────────────

async def check_quota(app: Client, uid: int, uname: str | None, chat_id: int) -> bool:
    if is_admin(uid, uname):
        return True
    usage = await get_daily_usage(uid)
    quota = await get_quota(uid)
    if usage >= quota:
        await app.send_message(
            chat_id,
            f"⚠️  <b>{bi('Cuota Diaria Agotada')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"Has utilizado  <b>{usage}/{quota}</b>  subidas hoy.\n"
            f"Tu cuota se renueva automáticamente a medianoche.\n\n"
            f"<i>¿Necesitas más? Contacta al administrador.</i>",
            parse_mode=PM,
            reply_markup=admin_contact_btn(),
        )
        return False
    return True


# ─── Verificar acceso ─────────────────────────────────────────────────────────

async def check_access(app: Client, message: Message) -> bool:
    if not message.from_user:
        return False
    uid   = message.from_user.id
    uname = message.from_user.username
    fname = message.from_user.first_name or "Usuario"

    if is_banned(uid, uname):
        await message.reply_text(
            f"🚫  <b>{bi('Cuenta Bloqueada')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"Tu cuenta ha sido bloqueada por el administrador.\n"
            f"Si crees que es un error, contáctalo directamente.",
            parse_mode=PM,
            reply_markup=admin_contact_btn(),
        )
        return False

    if not is_allowed(uid, uname):
        if _ADMIN_ID:
            try:
                await app.send_message(
                    _ADMIN_ID,
                    f"🔔  <b>{bi('Solicitud de Acceso')}</b>\n"
                    f"<code>{DIV}</code>\n\n"
                    f"👤  <b>{esc(fname)}</b>\n"
                    f"🆔  <code>{uid}</code>\n"
                    f"📧  @{esc(uname or 'sin_usuario')}",
                    parse_mode=PM,
                    reply_markup=InlineKeyboardMarkup([[
                        InlineKeyboardButton("✅ Aprobar", callback_data=f"approve_{uid}"),
                        InlineKeyboardButton("❌ Rechazar", callback_data=f"reject_{uid}"),
                    ]]),
                )
            except Exception:
                pass

        await message.reply_text(
            f"🔐  <b>{bi('Acceso Restringido')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"No tienes permiso para usar este bot.\n\n"
            f"Tu solicitud fue enviada al administrador.\n"
            f"Te notificaremos cuando sea aprobada. ✉️",
            parse_mode=PM,
            reply_markup=admin_contact_btn(),
        )
        return False

    return True


# ─── Procesador de trabajos ────────────────────────────────────────────────────

async def process_job(app: Client, job: dict):
    uid        = job["user_id"]
    chat_id    = job["chat_id"]
    uname      = job.get("username") or ""
    first_name = job.get("first_name") or ""
    job_type   = job["type"]
    cancel_ev  = job["cancel_event"]

    work_dir = TEMP_DIR / f"job_{uid}_{int(time.time() * 1000)}"
    work_dir.mkdir(parents=True, exist_ok=True)
    status_msg = None

    try:
        status_msg = await app.send_message(
            chat_id,
            f"🚀  <b>{bi('Procesando tu solicitud...')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"⏳  {bi('Preparando descarga...')}",
            parse_mode=PM,
            reply_markup=cancel_kb(uid),
        )
        smid = status_msg.id

        active_tasks[uid] = {
            "status": "Procesando",
            "cancel_event": cancel_ev,
            "progress_msg_id": smid,
            "chat_id": chat_id,
        }

        if cancel_ev.is_set():
            await safe_edit(app, chat_id, smid,
                f"⏹  <b>{bi('Tarea cancelada por el usuario.')}</b>")
            return

        # ── Descarga ───────────────────────────────────────────────────────────
        downloaded_files: list[Path] = []
        title = "archivo"

        if job_type == "file":
            original_msg: Message = job["message"]
            doc = (
                original_msg.document or original_msg.video or original_msg.audio
                or original_msg.voice or original_msg.video_note
                or original_msg.animation or original_msg.photo
            )
            fname = getattr(doc, "file_name", None) or "archivo"
            stem   = Path(fname).stem
            raw_suffix = Path(fname).suffix
            if not raw_suffix:
                if original_msg.photo:
                    raw_suffix = ".jpg"
                elif original_msg.voice:
                    raw_suffix = ".ogg"
                elif original_msg.video or original_msg.video_note:
                    raw_suffix = ".mp4"
                elif original_msg.audio:
                    raw_suffix = ".mp3"
                else:
                    raw_suffix = ".bin"
            suffix = raw_suffix
            dest   = work_dir / (sanitize_name(stem) + suffix)
            title  = stem

            ok = await download_telegram_file_mtproto(
                app, original_msg, dest, chat_id, smid, cancel_ev
            )
            if ok and dest.exists():
                downloaded_files = [dest]

        elif job_type == "platform":
            url      = job["url"]
            quality  = job.get("quality", "best")
            playlist = job.get("playlist", False)
            files, title = await download_platform(
                url, work_dir, quality, chat_id, smid, app, cancel_ev, playlist
            )
            downloaded_files = files

        elif job_type == "url":
            url = job["url"]
            f, title = await download_url_direct(url, work_dir, chat_id, smid, app, cancel_ev)
            if f:
                downloaded_files = [f]

        if cancel_ev.is_set():
            await safe_edit(app, chat_id, smid,
                f"⏹  <b>{bi('Tarea cancelada por el usuario.')}</b>")
            return

        if not downloaded_files:
            await safe_edit(
                app, chat_id, smid,
                f"❌  <b>{bi('Error al descargar')}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"No se pudo obtener el archivo.\n"
                f"Verifica el enlace e intenta de nuevo.",
            )
            return

        # ── Comprimir y subir ──────────────────────────────────────────────────
        for file_path in downloaded_files:
            if cancel_ev.is_set():
                break

            file_title   = file_path.stem if len(downloaded_files) > 1 else title
            archive_name = sanitize_name(file_title)

            try:
                archive_path = await compress_file_with_progress(
                    file_path, work_dir, archive_name, chat_id, smid, app, cancel_ev
                )
            except asyncio.CancelledError:
                break
            except Exception as e:
                await safe_edit(app, chat_id, smid,
                    f"❌  <b>{bi('Error al comprimir')}</b>\n\n"
                    f"<code>{esc(str(e)[:200])}</code>")
                continue

            if cancel_ev.is_set():
                break

            try:
                link, identifier = await upload_to_cloud(
                    archive_path, file_title, chat_id, smid, app, cancel_ev
                )
            except Exception as e:
                await safe_edit(app, chat_id, smid,
                    f"❌  <b>{bi('Error al subir a la nube')}</b>\n\n"
                    f"<code>{esc(str(e)[:200])}</code>")
                continue

            archive_size = archive_path.stat().st_size
            await add_history(uid, uname, first_name, file_title, link, archive_size)
            await increment_usage(uid)

            try:
                await app.delete_messages(chat_id, smid)
            except Exception:
                pass

            await send_result_txt(app, chat_id, file_title, link, identifier, archive_size)

            if _ADMIN_ID and uid != _ADMIN_ID:
                try:
                    await app.send_message(
                        _ADMIN_ID,
                        f"📤  <b>{bi('Nueva subida completada')}</b>\n"
                        f"<code>{DIV}</code>\n\n"
                        f"👤  <b>{esc(first_name)}</b>  (@{esc(uname or '—')})\n"
                        f"🆔  <code>{uid}</code>\n"
                        f"📂  <b>{esc(file_title[:50])}</b>\n"
                        f"📦  {bi(fmt_size(archive_size))}\n\n"
                        f'🔗  <a href="{link}">Descargar archivo</a>',
                        parse_mode=PM,
                        disable_web_page_preview=True,
                    )
                except Exception:
                    pass

    except Exception as e:
        logger.error(f"Error en process_job: {e}", exc_info=True)
        if status_msg:
            try:
                await safe_edit(app, chat_id, status_msg.id,
                    f"❌  <b>{bi('Error inesperado')}</b>\n\n"
                    f"<code>{esc(str(e)[:200])}</code>")
            except Exception:
                pass
    finally:
        active_tasks.pop(uid, None)
        shutil.rmtree(work_dir, ignore_errors=True)


def _cleanup_pending(d: dict, max_entries: int = 200):
    if len(d) > max_entries:
        keys_to_del = list(d.keys())[: len(d) - max_entries]
        for k in keys_to_del:
            d.pop(k, None)


async def enqueue_job(app: Client, uid: int, job: dict) -> int:
    if uid not in job_queues:
        job_queues[uid] = asyncio.Queue()
        asyncio.create_task(queue_worker(app, uid))
    pos = job_queues[uid].qsize()
    job["cancel_event"] = asyncio.Event()
    await job_queues[uid].put(job)
    _cleanup_pending(pending_quality)
    _cleanup_pending(pending_playlist)
    return pos


async def queue_worker(app: Client, uid: int):
    while True:
        job = await job_queues[uid].get()
        try:
            await process_job(app, job)
        except Exception as e:
            logger.error(f"queue_worker uid={uid}: {e}", exc_info=True)
        finally:
            job_queues[uid].task_done()


# ─── Comandos ─────────────────────────────────────────────────────────────────

async def cmd_start(app: Client, message: Message):
    uid   = message.from_user.id
    uname = message.from_user.username
    fname = esc(message.from_user.first_name or "Usuario")

    if is_banned(uid, uname):
        await message.reply_text(
            f"🚫  <b>{bi('Cuenta Bloqueada')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"Tu cuenta ha sido bloqueada. Contacta al administrador.",
            parse_mode=PM,
            reply_markup=admin_contact_btn(),
        )
        return

    if not is_allowed(uid, uname):
        await message.reply_text(
            f"🔐  <b>{bi('Acceso Restringido')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"No tienes permiso para usar este bot.\n"
            f"Contacta al administrador para solicitar acceso.",
            parse_mode=PM,
            reply_markup=admin_contact_btn(),
        )
        return

    admin_badge = "  👑" if is_admin(uid, uname) else ""
    usage = await get_daily_usage(uid)
    quota = await get_quota(uid)
    quota_str = "∞" if is_admin(uid, uname) else str(quota)

    await message.reply_text(
        f"🤖  <b>{bi('Bot Archivador')}  ·  v3.1</b>{admin_badge}\n"
        f"<code>{DIV}</code>\n\n"
        f"👋  <b>{bi(f'Bienvenido, {fname}!')}</b>\n\n"
        f"📌  Envíame cualquiera de estos:\n\n"
        f"  📁  Archivo de Telegram  <i>(hasta 2 GB)</i>\n"
        f"  🎬  YouTube · Playlist completa\n"
        f"  📸  Instagram · TikTok · Twitter/X\n"
        f"  🌐  Cualquier enlace de descarga\n\n"
        f"📊  <b>Uso hoy:</b>  {bi(str(usage))}/{bi(quota_str)}\n\n"
        f"<i>Escribe /help para ver los comandos disponibles.</i>",
        parse_mode=PM,
    )


async def cmd_help(app: Client, message: Message):
    if not await check_access(app, message):
        return
    uid   = message.from_user.id
    uname = message.from_user.username

    admin_section = ""
    if is_admin(uid, uname):
        admin_section = (
            f"\n\n👑  <b>{bi('Comandos de Administrador')}</b>\n"
            f"<code>{DIV}</code>\n"
            f"  /add_user   —  Agregar usuario por ID o @usuario\n"
            f"  /ban_user   —  Banear usuario\n"
            f"  /list_user  —  Ver todos los usuarios\n"
            f"  /set_cuota  —  Cambiar cuota diaria de un usuario"
        )

    await message.reply_text(
        f"📋  <b>{bi('Comandos Disponibles')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"  /start      —  Inicio y bienvenida\n"
        f"  /help       —  Este mensaje de ayuda\n"
        f"  /status     —  Estado de tu tarea actual\n"
        f"  /cancelar   —  Cancelar tarea en curso\n"
        f"  /historial  —  Tus últimas 10 subidas"
        + admin_section,
        parse_mode=PM,
    )


async def cmd_status(app: Client, message: Message):
    if not await check_access(app, message):
        return
    uid = message.from_user.id
    task = active_tasks.get(uid)
    queue_size = job_queues[uid].qsize() if uid in job_queues else 0

    if not task and queue_size == 0:
        await message.reply_text(
            f"✅  <b>{bi('Sin tareas activas')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"No tienes ninguna tarea en proceso.\n"
            f"Envíame un archivo o enlace para comenzar.",
            parse_mode=PM,
        )
    elif task:
        cola_txt = f"\n📋  {bi(str(queue_size))} más en cola" if queue_size > 0 else ""
        await message.reply_text(
            f"⚙️  <b>{bi('Tarea en proceso')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"🔄  {bi(task.get('status', 'Procesando'))}"
            + cola_txt
            + f"\n\n<i>Usa /cancelar para detenerla.</i>",
            parse_mode=PM,
        )
    else:
        await message.reply_text(
            f"⏳  <b>{bi('Cola de espera')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"📋  {bi(str(queue_size))} tarea(s) en cola.",
            parse_mode=PM,
        )


async def cmd_cancelar(app: Client, message: Message):
    if not await check_access(app, message):
        return
    uid = message.from_user.id
    task = active_tasks.get(uid)
    if task:
        task["cancel_event"].set()
        await message.reply_text(
            f"⏹  <b>{bi('Cancelando...')}</b>\n\n"
            f"La tarea en curso será detenida.",
            parse_mode=PM,
        )
    else:
        await message.reply_text(
            f"ℹ️  <b>{bi('Sin tareas activas')}</b>\n\n"
            f"No tienes ninguna tarea en proceso ahora mismo.",
            parse_mode=PM,
        )


async def cmd_historial(app: Client, message: Message):
    if not await check_access(app, message):
        return
    uid = message.from_user.id
    rows = await get_history(uid, limit=10)
    if not rows:
        await message.reply_text(
            f"📋  <b>{bi('Historial vacío')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"No has subido ningún archivo aún.\n"
            f"¡Envíame algo para comenzar! 🚀",
            parse_mode=PM,
        )
        return

    lines = [
        f"📋  <b>{bi('Tus últimas subidas')}</b>",
        f"<code>{DIV}</code>",
        "",
    ]
    for i, (fname, link, size, created_at) in enumerate(rows, 1):
        lines.append(
            f"<b>{bi(str(i))}.</b>  {esc(fname[:40])}\n"
            f"     📦 {fmt_size(size)}  ·  📅 {created_at}\n"
            f"     <a href=\"{link}\">📥 Descargar</a>"
        )
    await message.reply_text(
        "\n\n".join(lines),
        parse_mode=PM,
        disable_web_page_preview=True,
    )




async def cmd_add_user(app: Client, message: Message):
    uid   = message.from_user.id
    uname = message.from_user.username
    if not is_admin(uid, uname):
        await message.reply_text(f"⛔  {bi('Solo el administrador puede usar este comando.')}", parse_mode=PM)
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        await message.reply_text(
            f"❓  <b>{bi('Uso:')}</b>\n\n"
            f"<code>/add_user [ID o @usuario]</code>\n\n"
            f"Ejemplos:\n  • <code>/add_user 123456789</code>\n  • <code>/add_user @nombre</code>",
            parse_mode=PM,
        )
        return

    raw = parts[1].strip().lstrip("@")
    try:
        entry = int(raw)
    except ValueError:
        entry = raw.lower()

    data = load_users()
    se = str(entry).lower()
    data["banned"] = [x for x in data["banned"] if str(x).lower() != se]
    if se not in [str(x).lower() for x in data["allowed"]]:
        data["allowed"].append(entry)
        save_users(data)
        await message.reply_text(
            f"✅  <b>{bi('Usuario Agregado')}</b>\n\n"
            f"👤  <code>{entry}</code>  ya tiene acceso al bot.",
            parse_mode=PM,
        )
        if isinstance(entry, int):
            try:
                await app.send_message(
                    entry,
                    f"✅  <b>{bi('¡Acceso Aprobado!')}</b>\n"
                    f"<code>{DIV}</code>\n\n"
                    f"Ya puedes usar el bot.\n"
                    f"Envía /start para comenzar. 🚀",
                    parse_mode=PM,
                )
            except Exception:
                pass
    else:
        await message.reply_text(
            f"ℹ️  <code>{entry}</code> ya tiene acceso al bot.",
            parse_mode=PM,
        )


async def cmd_ban_user(app: Client, message: Message):
    uid   = message.from_user.id
    uname = message.from_user.username
    if not is_admin(uid, uname):
        await message.reply_text(f"⛔  {bi('Sin permiso.')}", parse_mode=PM)
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        await message.reply_text(
            f"❓  <b>{bi('Uso:')}</b>\n\n<code>/ban_user [ID o @usuario]</code>",
            parse_mode=PM,
        )
        return

    raw = parts[1].strip().lstrip("@")
    try:
        entry = int(raw)
    except ValueError:
        entry = raw.lower()

    if isinstance(entry, int) and _ADMIN_ID and entry == _ADMIN_ID:
        await message.reply_text(f"❌  {bi('No puedes banear al administrador.')}", parse_mode=PM)
        return

    data = load_users()
    se = str(entry).lower()
    data["allowed"] = [x for x in data["allowed"] if str(x).lower() != se]
    if se not in [str(x).lower() for x in data["banned"]]:
        data["banned"].append(entry)
        save_users(data)
        await message.reply_text(
            f"🚫  <b>{bi('Usuario Baneado')}</b>\n\n"
            f"👤  <code>{entry}</code>  ya no tiene acceso.",
            parse_mode=PM,
        )
    else:
        await message.reply_text(f"ℹ️  <code>{entry}</code> ya estaba baneado.", parse_mode=PM)


async def cmd_list_user(app: Client, message: Message):
    uid   = message.from_user.id
    uname = message.from_user.username
    if not is_admin(uid, uname):
        await message.reply_text(f"⛔  {bi('Sin permiso.')}", parse_mode=PM)
        return

    data = load_users()
    allowed = data.get("allowed", [])
    banned  = data.get("banned", [])

    def tag(u):
        adm = (isinstance(u, int) and _ADMIN_ID and u == _ADMIN_ID) or \
              (isinstance(u, str) and _ADMIN_USERNAME and u.lower() == _ADMIN_USERNAME)
        return f"  {'👑' if adm else '👤'}  <code>{u}</code>"

    allowed_lines = [tag(u) for u in allowed] if allowed else ["  —"]
    banned_lines  = [f"  🚫  <code>{u}</code>" for u in banned] if banned else ["  —"]

    lines = [
        f"👥  <b>{bi('Gestión de Usuarios')}</b>",
        f"<code>{DIV}</code>", "",
        f"✅  <b>Con acceso</b>  ({len(allowed)})",
        *allowed_lines, "",
        f"🚫  <b>Baneados</b>  ({len(banned)})",
        *banned_lines, "",
        f"<code>{DIV}</code>",
        f"📊  <b>Total:</b>  {len(allowed)} activos  ·  {len(banned)} baneados",
    ]
    await message.reply_text("\n".join(lines), parse_mode=PM)


async def cmd_set_cuota(app: Client, message: Message):
    uid   = message.from_user.id
    uname = message.from_user.username
    if not is_admin(uid, uname):
        await message.reply_text(f"⛔  {bi('Sin permiso.')}", parse_mode=PM)
        return

    parts = message.text.split()
    if len(parts) < 3:
        await message.reply_text(
            f"❓  <b>{bi('Uso:')}</b>\n\n"
            f"<code>/set_cuota [ID o @usuario] [límite_diario]</code>\n\n"
            f"Ejemplos:\n"
            f"  • <code>/set_cuota 123456789 20</code>\n"
            f"  • <code>/set_cuota @nombre 20</code>",
            parse_mode=PM,
        )
        return

    raw_target = parts[1].lstrip("@")
    try:
        limit = int(parts[2])
    except ValueError:
        await message.reply_text("❌  El límite debe ser un número entero.", parse_mode=PM)
        return

    # Resolver ID numérico o @usuario
    target_uid: int | None = None
    display = raw_target
    if raw_target.lstrip("-").isdigit():
        target_uid = int(raw_target)
    else:
        try:
            user_obj = await app.get_users(raw_target)
            target_uid = user_obj.id
            display = f"@{raw_target}"
        except Exception:
            await message.reply_text(
                f"❌  No se pudo encontrar al usuario <code>@{esc(raw_target)}</code>.\n\n"
                f"Asegúrate de que el usuario haya iniciado una conversación con el bot.",
                parse_mode=PM,
            )
            return

    await set_quota(target_uid, limit)
    await message.reply_text(
        f"✅  <b>{bi('Cuota actualizada')}</b>\n\n"
        f"👤  <code>{display}</code>\n"
        f"📊  Nueva cuota:  <b>{limit}</b> subidas/día",
        parse_mode=PM,
    )


# ─── Handlers de archivos y texto ─────────────────────────────────────────────

async def handle_file(app: Client, message: Message):
    if not await check_access(app, message):
        return
    uid   = message.from_user.id
    uname = message.from_user.username

    if not await check_quota(app, uid, uname, message.chat.id):
        return

    pos = await enqueue_job(app, uid, {
        "user_id":    uid,
        "chat_id":    message.chat.id,
        "username":   uname,
        "first_name": message.from_user.first_name or "",
        "type":       "file",
        "message":    message,
    })
    if pos > 0:
        await message.reply_text(
            f"📋  <b>{bi('En cola')}</b>\n\n"
            f"Tu archivo está en la posición  <b>{bi(str(pos + 1))}</b>.\n"
            f"Se procesará en cuanto termine la tarea anterior.",
            parse_mode=PM,
        )


async def handle_text(app: Client, message: Message):
    if not await check_access(app, message):
        return

    text = message.text or message.caption or ""
    url  = extract_url(text)

    if not url:
        await message.reply_text(
            f"💡  <b>{bi('¿Cómo usar el bot?')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"  📁  Envíame un archivo de Telegram  <i>(hasta 2 GB)</i>\n"
            f"  🎬  Enlace de YouTube o Playlist\n"
            f"  📸  Instagram · TikTok · Twitter/X\n"
            f"  🌐  Cualquier URL de descarga directa\n\n"
            f"<i>Escribe /help para ver todos los comandos.</i>",
            parse_mode=PM,
        )
        return

    uid   = message.from_user.id
    uname = message.from_user.username

    if not await check_quota(app, uid, uname, message.chat.id):
        return

    # Playlist de YouTube
    if is_youtube_playlist(url):
        key = str(uuid.uuid4())[:8]
        pending_playlist[key] = {
            "url": url, "user_id": uid, "chat_id": message.chat.id,
            "username": uname, "first_name": message.from_user.first_name or "",
        }
        await message.reply_text(
            f"🎵  <b>{bi('Playlist de YouTube detectada')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"🔗  <code>{esc(url[:70])}</code>\n\n"
            f"¿Qué deseas descargar?",
            parse_mode=PM,
            reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton("📋 Toda la playlist", callback_data=f"playlist_all_{key}"),
                InlineKeyboardButton("🎬 Solo este video",  callback_data=f"playlist_one_{key}"),
            ]]),
        )
        return

    # Plataformas: selector de calidad
    if is_platform_url(url):
        key = str(uuid.uuid4())[:8]
        pending_quality[key] = {
            "url": url, "user_id": uid, "chat_id": message.chat.id,
            "username": uname, "first_name": message.from_user.first_name or "",
            "playlist": False,
        }
        await message.reply_text(
            f"🎬  <b>{bi('Selecciona la calidad')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"🔗  <code>{esc(url[:70])}</code>",
            parse_mode=PM,
            reply_markup=InlineKeyboardMarkup([
                [
                    InlineKeyboardButton("⭐ Mejor calidad", callback_data=f"quality_best_{key}"),
                    InlineKeyboardButton("📺 1080p",         callback_data=f"quality_1080_{key}"),
                ],
                [
                    InlineKeyboardButton("📺 720p",          callback_data=f"quality_720_{key}"),
                    InlineKeyboardButton("📺 480p",          callback_data=f"quality_480_{key}"),
                ],
                [
                    InlineKeyboardButton("📺 360p",          callback_data=f"quality_360_{key}"),
                    InlineKeyboardButton("🎵 Solo audio",    callback_data=f"quality_audio_{key}"),
                ],
            ]),
        )
        return

    # URL directa
    pos = await enqueue_job(app, uid, {
        "user_id":    uid,
        "chat_id":    message.chat.id,
        "username":   uname,
        "first_name": message.from_user.first_name or "",
        "type":       "url",
        "url":        url,
    })
    if pos > 0:
        await message.reply_text(
            f"📋  <b>{bi(f'En cola — posición {pos + 1}')}</b>",
            parse_mode=PM,
        )


# ─── Handler de callbacks ─────────────────────────────────────────────────────

async def handle_callback(app: Client, callback: CallbackQuery):
    data = callback.data or ""
    uid  = callback.from_user.id

    # Cancelar
    if data.startswith("cancel_"):
        try:
            task_uid = int(data.split("_", 1)[1])
        except ValueError:
            await callback.answer("Datos inválidos.", show_alert=True)
            return
        if uid != task_uid and not is_admin(uid, callback.from_user.username):
            await callback.answer("No tienes permiso.", show_alert=True)
            return
        task = active_tasks.get(task_uid)
        if task:
            task["cancel_event"].set()
            await callback.answer("⏹ Operación cancelada", show_alert=False)
            try:
                await callback.message.edit_text(
                    f"⏹  <b>{bi('Operación cancelada')}</b>\n"
                    f"<code>{DIV}</code>\n\n"
                    f"La tarea fue detenida al instante.",
                    parse_mode=PM,
                )
            except Exception:
                pass
        else:
            await callback.answer("No hay tarea activa.", show_alert=True)
        return

    # Calidad
    if data.startswith("quality_"):
        parts = data.split("_", 2)
        if len(parts) < 3:
            await callback.answer("Datos inválidos.", show_alert=True)
            return
        quality, key = parts[1], parts[2]
        info = pending_quality.pop(key, None)
        if not info or info["user_id"] != uid:
            await callback.answer("Esta selección ya no es válida.", show_alert=True)
            return

        qlabel = QUALITY_LABELS.get(quality, quality)
        await callback.answer(f"✅ {qlabel}")
        try:
            await callback.message.delete()
        except Exception:
            pass

        pos = await enqueue_job(app, uid, {
            "user_id":    uid,
            "chat_id":    info["chat_id"],
            "username":   info["username"],
            "first_name": info["first_name"],
            "type":       "platform",
            "url":        info["url"],
            "quality":    quality,
            "playlist":   info.get("playlist", False),
        })
        if pos > 0:
            await app.send_message(
                info["chat_id"],
                f"📋  <b>{bi(f'En cola — posición {pos + 1}')}</b>",
                parse_mode=PM,
            )
        return

    # Playlist
    if data.startswith("playlist_"):
        parts = data.split("_", 2)
        if len(parts) < 3:
            await callback.answer("Datos inválidos.", show_alert=True)
            return
        mode, key = parts[1], parts[2]
        info = pending_playlist.pop(key, None)
        if not info or info["user_id"] != uid:
            await callback.answer("Esta selección ya no es válida.", show_alert=True)
            return

        playlist_mode = (mode == "all")
        await callback.answer("✅ Seleccionado")
        try:
            await callback.message.delete()
        except Exception:
            pass

        qual_key = str(uuid.uuid4())[:8]
        pending_quality[qual_key] = {
            "url":        info["url"],
            "user_id":    uid,
            "chat_id":    info["chat_id"],
            "username":   info["username"],
            "first_name": info["first_name"],
            "playlist":   playlist_mode,
        }
        await app.send_message(
            info["chat_id"],
            f"🎬  <b>{bi('Selecciona la calidad')}</b>\n"
            f"<code>{DIV}</code>",
            parse_mode=PM,
            reply_markup=InlineKeyboardMarkup([
                [
                    InlineKeyboardButton("⭐ Mejor calidad", callback_data=f"quality_best_{qual_key}"),
                    InlineKeyboardButton("📺 1080p",         callback_data=f"quality_1080_{qual_key}"),
                ],
                [
                    InlineKeyboardButton("📺 720p",          callback_data=f"quality_720_{qual_key}"),
                    InlineKeyboardButton("📺 480p",          callback_data=f"quality_480_{qual_key}"),
                ],
                [
                    InlineKeyboardButton("📺 360p",          callback_data=f"quality_360_{qual_key}"),
                    InlineKeyboardButton("🎵 Solo audio",    callback_data=f"quality_audio_{qual_key}"),
                ],
            ]),
        )
        return

    # Aprobar / Rechazar acceso
    if data.startswith("approve_") or data.startswith("reject_"):
        if not is_admin(uid, callback.from_user.username):
            await callback.answer("Solo el administrador puede hacer esto.", show_alert=True)
            return

        action, target_str = data.split("_", 1)
        try:
            target_uid = int(target_str)
        except ValueError:
            await callback.answer("Datos inválidos.", show_alert=True)
            return

        if action == "approve":
            data_users = load_users()
            se = str(target_uid)
            data_users["banned"] = [x for x in data_users["banned"] if str(x) != se]
            if target_uid not in data_users["allowed"]:
                data_users["allowed"].append(target_uid)
                save_users(data_users)

            await callback.answer("✅ Usuario aprobado")
            try:
                await callback.message.edit_text(
                    callback.message.text + "\n\n✅  <b>Aprobado por el administrador.</b>",
                    parse_mode=PM,
                )
            except Exception:
                pass
            try:
                await app.send_message(
                    target_uid,
                    f"✅  <b>{bi('¡Acceso Aprobado!')}</b>\n"
                    f"<code>{DIV}</code>\n\n"
                    f"Ya puedes usar el bot.\n"
                    f"Envía /start para comenzar. 🚀",
                    parse_mode=PM,
                )
            except Exception:
                pass
        else:
            await callback.answer("❌ Solicitud rechazada")
            try:
                await callback.message.edit_text(
                    callback.message.text + "\n\n❌  <b>Rechazado por el administrador.</b>",
                    parse_mode=PM,
                )
            except Exception:
                pass
            try:
                await app.send_message(
                    target_uid,
                    f"❌  <b>{bi('Solicitud Rechazada')}</b>\n"
                    f"<code>{DIV}</code>\n\n"
                    f"El administrador ha rechazado tu solicitud de acceso.",
                    parse_mode=PM,
                    reply_markup=admin_contact_btn(),
                )
            except Exception:
                pass
        return

    await callback.answer()


# ─── Servidor de salud ────────────────────────────────────────────────────────

class HealthHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.end_headers()
        self.wfile.write(b"OK")

    def log_message(self, *args):
        pass


def start_health_server():
    for attempt in range(5):
        try:
            server = HTTPServer(("0.0.0.0", HEALTH_PORT), HealthHandler)
            t = threading.Thread(target=server.serve_forever, daemon=True)
            t.start()
            logger.info(f"Servidor de salud en puerto {HEALTH_PORT}")
            return
        except OSError:
            if attempt < 4:
                time.sleep(2)
    logger.warning(f"Servidor de salud no disponible (puerto {HEALTH_PORT} ocupado)")


# ─── Main ─────────────────────────────────────────────────────────────────────

def _validate_config() -> list[str]:
    errors = []
    # Token de Telegram: formato "123456:ABCdef..." (id numérico + ":" + hash)
    _token_parts = BOT_TOKEN.split(":", 1)
    if not BOT_TOKEN or len(_token_parts) != 2 or not _token_parts[0].isdigit() or len(_token_parts[1]) < 10:
        errors.append("TELEGRAM_BOT_TOKEN — falta o tiene valor de ejemplo")
    if not API_ID:
        errors.append("TELEGRAM_API_ID — falta o no es un número válido")
    if not API_HASH or len(API_HASH) < 10:
        errors.append("TELEGRAM_API_HASH — falta o tiene valor de ejemplo")
    if not ARCHIVE_ACCESS or len(ARCHIVE_ACCESS) < 10:
        errors.append("ARCHIVE_ORG_ACCESS_KEY — falta o tiene valor de ejemplo")
    if not ARCHIVE_SECRET or len(ARCHIVE_SECRET) < 10:
        errors.append("ARCHIVE_ORG_SECRET_KEY — falta o tiene valor de ejemplo")
    return errors


async def main():
    await init_db()

    config_errors = _validate_config()
    if config_errors:
        logger.error("=" * 60)
        logger.error("❌ ERROR: Variables de entorno no configuradas:")
        for e in config_errors:
            logger.error(f"   • {e}")
        logger.error("Por favor rellena el archivo .env con tus credenciales reales.")
        logger.error("=" * 60)
        return

    start_health_server()

    app = Client(
        "bot_session",
        api_id=API_ID,
        api_hash=API_HASH,
        bot_token=BOT_TOKEN,
        workdir=str(Path(__file__).parent),
    )

    # Comandos
    app.on_message(filters.command("start")     & filters.private)(cmd_start)
    app.on_message(filters.command("help")      & filters.private)(cmd_help)
    app.on_message(filters.command("status")    & filters.private)(cmd_status)
    app.on_message(filters.command("cancelar")  & filters.private)(cmd_cancelar)
    app.on_message(filters.command("historial") & filters.private)(cmd_historial)
    app.on_message(filters.command("add_user")  & filters.private)(cmd_add_user)
    app.on_message(filters.command("ban_user")  & filters.private)(cmd_ban_user)
    app.on_message(filters.command("list_user") & filters.private)(cmd_list_user)
    app.on_message(filters.command("set_cuota") & filters.private)(cmd_set_cuota)

    # Archivos (MTProto — hasta 2 GB)
    app.on_message(
        filters.private & (
            filters.document | filters.video | filters.audio |
            filters.voice | filters.video_note | filters.animation | filters.photo
        )
    )(handle_file)

    # Texto y URLs
    app.on_message(
        filters.private & filters.text
        & ~filters.command([
            "start", "help", "status", "cancelar", "historial",
            "add_user", "ban_user", "list_user", "set_cuota",
        ])
    )(handle_text)

    # Callbacks
    app.on_callback_query()(handle_callback)

    logger.info("Iniciando bot con Pyrogram (MTProto)...")
    await app.start()

    # Comandos para usuarios normales (barra de Telegram)
    user_commands = [
        BotCommand("start",     "🤖 Inicio y bienvenida"),
        BotCommand("help",      "📋 Comandos disponibles"),
        BotCommand("status",    "⚙️ Estado de tu tarea actual"),
        BotCommand("cancelar",  "⏹ Cancelar tarea en curso"),
        BotCommand("historial", "📂 Tus últimas 10 subidas"),
    ]
    await app.set_bot_commands(user_commands, scope=BotCommandScopeDefault())

    # Comandos exclusivos para el administrador
    admin_chat_id: int | str | None = _ADMIN_ID or (f"@{_ADMIN_USERNAME}" if _ADMIN_USERNAME else None)
    if admin_chat_id:
        admin_commands = user_commands + [
            BotCommand("add_user",  "👤 Agregar usuario"),
            BotCommand("ban_user",  "🚫 Banear usuario"),
            BotCommand("list_user", "👥 Ver todos los usuarios"),
            BotCommand("set_cuota", "📊 Cambiar cuota diaria"),
        ]
        try:
            await app.set_bot_commands(admin_commands, scope=BotCommandScopeChat(chat_id=admin_chat_id))
        except Exception as e:
            logger.warning(f"No se pudieron registrar comandos de admin: {e}")

    logger.info("✅ Bot v3.1 iniciado — listo para recibir mensajes")
    await idle()
    await app.stop()


if __name__ == "__main__":
    asyncio.run(main())
