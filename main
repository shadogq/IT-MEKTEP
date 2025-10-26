"""
fast stop fixed
optimization (current quarter only)
message templates adjusted
send long fix
exp backoff changed to fixed 120s
added teachers
global/partial removed
"""

import os
import sys
import time
import json
import asyncio
import logging
from datetime import datetime, timedelta
import traceback
import re
from typing import Dict, Any, Iterable, List, Tuple, Optional, Coroutine
from collections import deque, defaultdict, Counter
from urllib.parse import urlparse, parse_qs, urljoin
from itertools import groupby
from asyncio import Queue
import statistics
import psutil
import os
from html import escape
from html.parser import HTMLParser
import sqlite3

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from bs4 import BeautifulSoup
import aiohttp
from aiogram import Bot, Dispatcher, types, enums
from aiogram.exceptions import TelegramNetworkError, TelegramForbiddenError, TelegramBadRequest, TelegramRetryAfter
from default_class_subject_sites import DEFAULT_CLASS_SUBJECT_SITES as DEFAULT_CLASS_SUBJECT_SITES_DEFAULT

CLASS_NAME_LATIN_TO_CYRILLIC = str.maketrans({
    "A": "А",
    "B": "В",
    "C": "С",
    "E": "Е",
    "H": "Н",
    "K": "К",
    "M": "М",
    "O": "О",
    "P": "Р",
    "T": "Т",
    "X": "Х",
    "Y": "У",
})


# ───────────────────────────────────────────────────────────────────────────────
# -2. HELPER CLASS FOR send_long
# ───────────────────────────────────────────────────────────────────────────────

class _SafeTelegramSplitter(HTMLParser):
    """
    Split an HTML snippet into correct pieces
    """
    _TAG_SYNONYM = {
        "strong": "b",
        "em":     "i",
        "ins":    "u",
        "strike": "s",
        "del":    "s",
    }
    _VOID_TAGS       = {"br"}
    _STACKABLE_TAGS  = {
        "b", "i", "u", "s",
        "code", "pre", "tg-spoiler",
        "a", "blockquote",
    }
    _ALLOWED_ATTR = {
        "a":          {"href"},
        "code":       {"class"},
        "pre":        {"class"},
        "blockquote": {"class"},
    }

    def __init__(self, original: str, max_len: int):
        super().__init__(convert_charrefs=False)
        self._max = max_len
        self._open_stack: List[Tuple[str, str]] = [] 
        self._part = ""
        self.parts: List[str] = []
        self.feed(original)
        self.close()

    def _build_attr_str(self, tag: str, attrs: List[Tuple[str, str]]) -> str:
        """keep only allowed attrs and escape their values"""
        keep = self._ALLOWED_ATTR.get(tag, set())
        out = []
        for k, v in attrs:
            if k in keep and v is not None:
                out.append(f'{k}="{escape(v, quote=True)}"')
        return (" " + " ".join(out)) if out else ""

    def _wrap_close(self) -> str:
        """closing tags in reverse order"""
        return "".join(f"</{tag}>" for tag, _ in reversed(self._open_stack))

    def _wrap_open(self) -> str:
        """opening tags to restart a new chunk"""
        return "".join(start for _, start in self._open_stack)

    def _flush_part(self):
        """close currently open tags, store the chunk, reopen them"""
        if not self._part and not self._open_stack:
            return
        chunk = self._part + self._wrap_close()
        if len(chunk) > self._max:
            chunk = escape(chunk)[: self._max]
        self.parts.append(chunk)
        self._part = self._wrap_open()

    def _write(self, s: str, raw: bool = False):
        txt = s if raw else escape(s)
        while txt:
            room = self._max - len(self._part) - len(self._wrap_close())
            if room <= 0:
                self._flush_part()
                continue

            self._part += txt[:room]
            txt = txt[room:]
            if txt:
                self._flush_part()

    def _write_tag(self, s: str):
        """write a (already escaped) tag, splitting if necessary"""
        if len(s) + len(self._part) + len(self._wrap_close()) > self._max:
            self._flush_part()
            if len(s) + len(self._wrap_close()) > self._max:
                raise ValueError(
                    f"Single HTML tag longer than max_length={self._max}: {s}"
                )
        self._part += s

    def handle_data(self, data):
        self._write(data)

    def handle_entityref(self, name):
        self._write(f"&{name};", raw=True)

    def handle_charref(self, name):
        self._write(f"&#{name};", raw=True)

    def handle_starttag(self, tag, attrs):
        orig_text = self.get_starttag_text() or ""
        tag = tag.lower()
        tag = self._TAG_SYNONYM.get(tag, tag)

        if tag == "span":
            for k, v in attrs:
                if k == "class" and v and "tg-spoiler" in v.lower():
                    tag, attrs = "tg-spoiler", []
                    break

        if tag not in self._STACKABLE_TAGS and tag not in self._VOID_TAGS:
            self._write(orig_text)
            return

        if tag in self._VOID_TAGS:
            if tag == "br":
                self._write("\n", raw=True)
            else:
                self._write_tag(f"<{tag}>")
            return

        attr_str = self._build_attr_str(tag, attrs)
        start_tag = f"<{tag}{attr_str}>"
        self._write_tag(start_tag)
        self._open_stack.append((tag, start_tag))

    def handle_endtag(self, tag):
        tag = tag.lower()
        tag = self._TAG_SYNONYM.get(tag, tag)

        if tag not in self._STACKABLE_TAGS:
            self._write(f"</{tag}>")
            return

        for i in range(len(self._open_stack) - 1, -1, -1):
            if self._open_stack[i][0] == tag:
                to_close = self._open_stack[i:]
                self._open_stack = self._open_stack[:i]
                for t, _ignored in reversed(to_close):
                    self._write_tag(f"</{t}>")
                for t, start in to_close[::-1][1:]:
                    self._open_stack.append((t, start))
                    self._write_tag(start)
                break
        else:
            self._write(f"</{tag}>")

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag.lower() not in self._VOID_TAGS:
            self.handle_endtag(tag)

    def close(self):
        super().close()
        self._flush_part()
        if not self.parts:
            self.parts.append("")



# ───────────────────────────────────────────────────────────────────────────────
# -1. MESSAGE QUEUE FOR SEND RATE LIMITING
# ───────────────────────────────────────────────────────────────────────────────
class MessageQueue:
    def __init__(self, bot_instance: Bot, logger_instance: 'Logger', rate_limit_per_second: int = 25):
        self._bot = bot_instance
        self._queue = asyncio.Queue()
        self._logger = logger_instance
        self._rate_limit_delay = 1.0 / rate_limit_per_second
        self._task: Optional[asyncio.Task] = None
        self._is_running = False
        self.telegram_send_errors = 0
        self.error_delay = 120
        self._tg_error_lock = asyncio.Lock()

    def get_queue_size(self) -> int:
        return self._queue.qsize()

    def get_worker_status(self) -> str:
        if self._task is None:
            return "Не запущен"
        if self._task.done():
            try:
                self._task.result() 
                return "Завершен"
            except asyncio.CancelledError:
                return "Отменен"
            except Exception as e:
                return f"Ошибка ({type(e).__name__})"
        elif self._is_running:
            return "Работает"
        else:
            return "Приостановлен (ожидает)" 

    async def _worker(self):
        self._logger.info("[MessageQueue] Worker started.")
        while self._is_running or not self._queue.empty():
            try:
                chat_id, text_content, message_type, send_kwargs = await asyncio.wait_for(self._queue.get(), timeout=1.0)
            except asyncio.TimeoutError:
                if not self._is_running and self._queue.empty():
                    self._logger.info("[MessageQueue] Worker stopping as queue is empty and not running.")
                    break
                continue
            except asyncio.CancelledError:
                self._logger.info("[MessageQueue] Worker task cancelled while waiting for queue item.")
                break

            retry_attempts = 2
            current_attempt = 0
            is_sent_successfully = False

            while current_attempt < retry_attempts:
                try:
                    if not self._is_running and current_attempt > 0 and not is_sent_successfully:
                        self._logger.info(f"[MessageQueue] Stop command received during retry for chat {chat_id}. Message will be requeued if queue processing is enabled.")
                        break

                    if message_type == "send":
                        await self._bot.send_message(chat_id, text_content, **send_kwargs)
                    elif message_type == "send_kb":
                        await self._bot.send_message(chat_id, text_content, **send_kwargs)
                    
                    is_sent_successfully = True
                    break

                except TelegramRetryAfter as e:
                    self._logger.warning(f"[MessageQueue] Rate limit hit for chat {chat_id}. Retrying after {e.retry_after}s. (Attempt {current_attempt + 1}/{retry_attempts})")
                    await asyncio.sleep(e.retry_after + 0.5)
                    current_attempt += 1
                except (aiohttp.ClientError, asyncio.TimeoutError, 
                        requests.exceptions.ConnectionError, requests.exceptions.Timeout) as e:
                    self._logger.warning(f"[MessageQueue] Network error for chat {chat_id} (Attempt {current_attempt + 1}/{retry_attempts}): {type(e).__name__} - {e}. Retrying...")
                    current_attempt += 1
                    if current_attempt < retry_attempts:
                        await asyncio.sleep(self.error_delay)
                    else:
                        self._logger.error(f"[MessageQueue] FINAL NETWORK FAILED to send to {chat_id} after {retry_attempts} attempts. Text: {text_content[:100]}")
                        async with self._tg_error_lock:
                            self.telegram_send_errors += 1
                except asyncio.CancelledError:
                    self._logger.info(f"[MessageQueue] Send operation for chat {chat_id} cancelled.")
                    is_sent_successfully = False
                    raise
                except Exception as e:
                    self._logger.error(f"[MessageQueue] Failed to send to {chat_id} (Attempt {current_attempt + 1}/{retry_attempts}): {type(e).__name__} - {e}. Text: {text_content[:100]}")
                    async with self._tg_error_lock:
                        self.telegram_send_errors += 1
                    current_attempt += 1
                    if current_attempt < retry_attempts:
                        await asyncio.sleep(self.error_delay)
                    else:
                        self._logger.error(f"[MessageQueue] FINAL FAILED to send to {chat_id} after {retry_attempts} attempts. Text: {text_content[:100]}")
                
            self._queue.task_done()
            if is_sent_successfully or current_attempt >= retry_attempts:
                await asyncio.sleep(self._rate_limit_delay)
        
        self._logger.info("[MessageQueue] Worker finished.")

    async def get_telegram_error_count(self) -> int:
        async with self._tg_error_lock:
            return self.telegram_send_errors

    async def add_to_queue(self, chat_id: int, text_content: str, message_type: str = "send", **kwargs):
        if not self._is_running and (self._task is None or self._task.done()):
             self._logger.warning("[MessageQueue] Queue was not running when a message was added. Attempting to restart worker.")
             self.start()
        elif self._task and self._task.done() and not self._is_running:
             self._logger.warning("[MessageQueue] Worker task was done but queue seems inactive. Attempting to restart worker.")
             self.start()

        if not self._is_running and not (self._task and not self._task.done()):
             self._logger.error("[MessageQueue] FAILED to ensure queue worker is running. Message will be queued but may not be sent if worker is truly down.")

        await self._queue.put((chat_id, text_content, message_type, kwargs))

    def start(self):
        if self._task is None or self._task.done():
            self._is_running = True
            self._task = asyncio.create_task(self._worker())
            self._logger.info("[MessageQueue] Queue worker task (re)started.")
        elif not self._is_running:
             self._is_running = True
             self._logger.info("[MessageQueue] Queue worker resumed (flag set to running). Existing task will continue if it was paused by flag.")

    async def stop(self, graceful_shutdown_timeout: float = 30.0, process_queue: bool = True):
        self._logger.info(f"[MessageQueue] Stopping queue worker (process_queue: {process_queue})...")
        
        if not self._task:
            self._logger.info("[MessageQueue] Worker task already None or never started. Stop sequence finished.")
            return

        self._is_running = False

        task_needs_cancellation = False
        worker_task_reference = self._task

        if process_queue:
            if not self._queue.empty():
                self._logger.info(f"[MessageQueue] Graceful stop: Waiting for {self._queue.qsize()} messages to be processed (max {graceful_shutdown_timeout}s)...")
                try:
                    await asyncio.wait_for(self._queue.join(), timeout=graceful_shutdown_timeout)
                    self._logger.info(f"[MessageQueue] Queue processing finished gracefully (all items processed or queue became empty).")
                except asyncio.TimeoutError:
                    self._logger.warning(f"[MessageQueue] Graceful shutdown timed out processing queue. {self._queue.qsize()} messages might be left. Will ensure worker task is cancelled.")
                    task_needs_cancellation = True
                except asyncio.CancelledError:
                    self._logger.warning("[MessageQueue] Stop operation was cancelled during queue.join. Will ensure worker task is cancelled.")
                    task_needs_cancellation = True
                except Exception as e:
                    self._logger.error(f"[MessageQueue] Error during queue.join on graceful stop: {e}. Will ensure worker task is cancelled.")
                    task_needs_cancellation = True
            else:
                self._logger.info("[MessageQueue] Graceful stop: Queue is already empty. Worker should exit naturally.")
        else:
            self._logger.info(f"[MessageQueue] Fast stop: Will ensure worker task is cancelled immediately.")
            task_needs_cancellation = True

        if task_needs_cancellation and not worker_task_reference.done():
            self._logger.info(f"[MessageQueue] Explicitly cancelling worker task now (Needed: {task_needs_cancellation}).")
            worker_task_reference.cancel()

        try:
            self._logger.info(f"[MessageQueue] Awaiting worker task termination (Task done before await: {worker_task_reference.done()})...")
            await worker_task_reference
            self._logger.info(f"[MessageQueue] Worker task awaited successfully (Task done after await: {worker_task_reference.done()}).")
        except asyncio.CancelledError:
            self._logger.info("[MessageQueue] Worker task was confirmed cancelled during final await.")
        except Exception as e:
            self._logger.error(f"[MessageQueue] Worker task threw an unhandled exception during final await: {type(e).__name__} - {e}")

        if worker_task_reference.done():
             exc = worker_task_reference.exception()
             if exc and not isinstance(exc, asyncio.CancelledError):
                 self._logger.error(f"[MessageQueue] Worker task finished with an unhandled exception: {exc}")
                 try:
                     traceback_str = "".join(traceback.format_exception(type(exc), exc, exc.__traceback__))
                     self._logger.error(f"[MessageQueue] Worker exception traceback:\n{traceback_str}")
                 except Exception as e_tb:
                     self._logger.error(f"[MessageQueue] Could not format traceback for worker exception: {e_tb}")
        elif not worker_task_reference.cancelled():
             self._logger.error("[MessageQueue] Worker task somehow not done and not cancelled after stop logic. This is unexpected.")


        if not process_queue:
            drained_count = 0
            while not self._queue.empty():
                try:
                    self._queue.get_nowait()
                    self._queue.task_done()
                    drained_count += 1
                except asyncio.QueueEmpty:
                    break 
                except Exception as e_drain:
                    self._logger.warning(f"[MessageQueue] Error draining item during fast stop finalization: {e_drain}")
                    break
            if drained_count > 0:
                self._logger.info(f"[MessageQueue] Drained {drained_count} items from queue during fast stop finalization.")

        self._task = None
        self._logger.info(f"[MessageQueue] Queue worker stop sequence fully finished (processed_queue: {process_queue}).")

MESSAGE_SENDER_QUEUE: Optional[MessageQueue] = None

# ───────────────────────────────────────────────────────────────────────────────
# 0. HELPER FUNCTIONS
# ───────────────────────────────────────────────────────────────────────────────
def parse_url_to_get_ids(url_str: str) -> Tuple[Optional[str], Optional[str]]:
    """Parses class_id and class_predmet_id from a mektep.edu.kz URL."""
    try:
        parsed_url = urlparse(url_str)
        query_params = parse_qs(parsed_url.query)
        class_id = query_params.get('class', [None])[0]
        predmet_id = query_params.get('predmet', [None])[0]
        return class_id, predmet_id
    except Exception:
        return None, None

# ───────────────────────────────────────────────────────────────────────────────
# 1. CONFIGURATION
# ───────────────────────────────────────────────────────────────────────────────
class Config:
    MAX_CONSECUTIVE_TEACHER_ID_FAILURES = 3
    TEACHER_ID_FAILURE_RESTART_COOLDOWN = 300
    DEFAULT_TEACHER_DIGEST_TIME = "08:00"
    DATABASE_NAME    = "bot_data.sqlite" 

    # ──────────────────────────────────────────────
    # TWEAKABLE PARAMETERS RESPONSIBLE FOR EFFICIENCY
    # ──────────────────────────────────────────────
    CHECK_INTERVAL   = 300 # how often current quarter is checked at max interval
    MEKTEP_CONCURRENT_REQUEST_LIMIT = 10 # max amount of concurrent HTTP requests
    MEKTEP_REQUEST_INTERVAL = 0.05 # gap between HTTP requests
    DEFAULT_NON_CURRENT_FETCH_INTERVAL = 43200*3 # how often all quarters (1-4) are checked

    # these credentials are to be filled in
    DEFAULT_USERNAME         = "" 
    DEFAULT_PASSWORD         = ""
    ADMIN_CHAT_ID            = 0
    TELEGRAM_TOKEN           = ""

    DEFAULT_LOGIN_URL        = "https://mektep.edu.kz/"
    DEFAULT_MEKTEP_ID        = "4" # this is an internal id of my school
    DEFAULT_CURRENT_YEAR     = "2025" # only the first academic year
    DEFAULT_CURRENT_MONITORING_QUARTER = 1 # must be manually changed every quarter (2-3 month)

    DEFAULT_CLASS_SUBJECT_SITES = DEFAULT_CLASS_SUBJECT_SITES_DEFAULT


    DEFAULT_CLASS_STUDENTS_URLS = { # these URLs are resposible for first extraction of students' names
        "11A": "https://mektep.edu.kz/office/?action=predmets&class=84655&predmet=20989",
        "11Б": "https://mektep.edu.kz/office/?action=predmets&class=84656&predmet=21028",
        "11В": "https://mektep.edu.kz/office/?action=predmets&class=84657&predmet=21198",
        "11Г": "https://mektep.edu.kz/office/?action=predmets&class=84658&predmet=32002",

        "10A": "https://mektep.edu.kz/office/?action=predmets&class=85719&predmet=20228",
        "10Б": "https://mektep.edu.kz/office/?action=predmets&class=85720&predmet=20801",
        "10В": "https://mektep.edu.kz/office/?action=predmets&class=85721&predmet=20895",
        "10Г": "https://mektep.edu.kz/office/?action=predmets&class=85722&predmet=21295",

        "9A": "https://mektep.edu.kz/office/?action=predmets&class=87916&predmet=13645",
        "9Б": "https://mektep.edu.kz/office/?action=predmets&class=87917&predmet=14209",
        "9В": "https://mektep.edu.kz/office/?action=predmets&class=87918&predmet=14668",
        "9Г": "https://mektep.edu.kz/office/?action=predmets&class=87919&predmet=15162",
        
        "8А": "https://mektep.edu.kz/office/?action=predmets&class=88828&predmet=11079",
        "8Б": "https://mektep.edu.kz/office/?action=predmets&class=88829&predmet=11494",
        "8В": "https://mektep.edu.kz/office/?action=predmets&class=88830&predmet=12081",
        "8Г": "https://mektep.edu.kz/office/?action=predmets&class=88832&predmet=12416",
        "8Д": "https://mektep.edu.kz/office/?action=predmets&class=88833&predmet=13000"
    }

    LOGIN_URL: str
    USERNAME: str
    PASSWORD: str
    MEKTEP_ID: str
    CURRENT_YEAR: str
    CURRENT_MONITORING_QUARTER: int
    CLASS_SUBJECT_SITES: Dict[str, Dict[str, str]]
    CLASS_STUDENTS_URLS: Dict[str, str]

    def __init__(self):
        self.LOGIN_URL = self.DEFAULT_LOGIN_URL
        self.USERNAME = self.DEFAULT_USERNAME
        self.PASSWORD = self.DEFAULT_PASSWORD
        self.MEKTEP_ID = self.DEFAULT_MEKTEP_ID
        self.CURRENT_YEAR = self.DEFAULT_CURRENT_YEAR
        self.CURRENT_MONITORING_QUARTER = self.DEFAULT_CURRENT_MONITORING_QUARTER
        self.CLASS_SUBJECT_SITES = self.DEFAULT_CLASS_SUBJECT_SITES
        self.CLASS_STUDENTS_URLS = self.DEFAULT_CLASS_STUDENTS_URLS
        self.NON_CURRENT_FETCH_INTERVAL = self.DEFAULT_NON_CURRENT_FETCH_INTERVAL


# ───────────────────────────────────────────────────────────────────────────────
# 2. ASYNC LOGGER
# ───────────────────────────────────────────────────────────────────────────────
class Logger:
    def __init__(self):
        logging.basicConfig(
            level=logging.INFO,
            format="%(asctime)s %(levelname)s: %(message)s",
            datefmt="%Y-%m-%d %H:%M:%S",
        )
        self.buf = deque(maxlen=200)
        self.bot: Optional[Bot] = None 
        self.admin_chat_id: Optional[int] = None

    def _log_to_buffer_and_tg(self, level_name: str, msg: str, is_exception: bool = False, tb: Optional[str] = None):
        timestamp = time.strftime('%Y-%m-%d %H:%M:%S')
        if is_exception and tb:
            self.buf.append(f"X {timestamp} {tb}")
            tg_msg = f"EXCEPTION:\n{tb[:4000]}"
        else:
            self.buf.append(f"{level_name[0]} {timestamp} {msg}")
            tg_msg = f"{level_name}: {msg}"

        if self.bot and self.admin_chat_id and level_name in ["ERROR", "EXCEPTION", "WARNING"]:
            try:
                if MESSAGE_SENDER_QUEUE:
                    asyncio.create_task(MESSAGE_SENDER_QUEUE.add_to_queue(self.admin_chat_id, tg_msg, message_type="send", parse_mode=None))
                else:
                    logging.error("Logger: MessageQueue not available for Telegram logging. Trying direct send.")
                    try:
                        loop = asyncio.get_running_loop()
                        loop.create_task(self.bot.send_message(self.admin_chat_id, tg_msg))
                    except RuntimeError:
                         logging.error("Logger: No running event loop for fallback send_message.")

            except RuntimeError:
                logging.error("Logger: Could not send Telegram message, no running event loop or queue issues.")
            except Exception as e_tg_log:
                logging.error(f"Logger: Exception during TG log send: {e_tg_log}")

    def info(self, msg: str):
        logging.info(msg)
        self._log_to_buffer_and_tg("INFO", msg)

    def debug(self, msg: str):
        logging.debug(msg)
        self._log_to_buffer_and_tg("DEBUG", msg)

    def warning(self, msg: str):
        logging.warning(msg)
        self._log_to_buffer_and_tg("WARNING", msg)

    def error(self, msg: str):
        logging.error(msg)
        self._log_to_buffer_and_tg("ERROR", msg)

    def exception(self, exc: Exception): 
        tb = traceback.format_exc()
        logging.error(f"EXCEPTION: {exc}\n{tb}")
        self._log_to_buffer_and_tg("EXCEPTION", str(exc), is_exception=True, tb=tb)


    def get_logs(self) -> str:
        return "\n".join(self.buf)

LOGGER = Logger()

# ───────────────────────────────────────────────────────────────────────────────
# 3. ASYNC HTTP DATA FETCHER
# ───────────────────────────────────────────────────────────────────────────────
class AsyncHTTPDataFetcher:
    BASE_HEADERS = {
        "Accept": "application/json, text/javascript, */*; q=0.01",
        "Accept-Language": "ru,en-GB;q=0.9,en;q=0.8,en-US;q=0.7",
        "Connection": "keep-alive",
        "Sec-Fetch-Dest": "empty", "Sec-Fetch-Mode": "cors", "Sec-Fetch-Site": "same-origin",
        "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"),
        "X-Requested-With": "XMLHttpRequest",
        "sec-ch-ua": '"Chromium";v="124", "Google Chrome";v="124", "Not-A.Brand";v="99"',
        "sec-ch-ua-mobile": "?0", "sec-ch-ua-platform": '"Windows"',
    }

    def __init__(self, cfg: Config, logger: Logger):
        self.cfg = cfg 
        self.log = logger
        self.session: Optional[requests.Session] = None
        self.loop = asyncio.get_running_loop()
        self._login_lock = asyncio.Lock()
        self._is_logged_in = False

        self.total_api_calls = 0
        self.api_errors = 0
        self.api_timeouts = 0
        self._stats_lock = asyncio.Lock()

        self._mektep_semaphore = asyncio.Semaphore(self.cfg.MEKTEP_CONCURRENT_REQUEST_LIMIT)
        self._last_mektep_request_time: float = 0.0 
        self._mektep_request_time_lock = asyncio.Lock() 

        self.login_url_base = urlparse(self.cfg.LOGIN_URL).scheme + "://" + urlparse(self.cfg.LOGIN_URL).netloc
        self.office_url = urljoin(self.login_url_base, "/office/") 
        self.ajax_url_base = urljoin(self.login_url_base, "/_monitor/__jurnal_form.php")

    async def _run_sync(self, func, *args) -> Any:
        return await self.loop.run_in_executor(None, func, *args)

    async def _ensure_request_interval(self):
        """Ensures that requests are spaced out by at least MEKTEP_REQUEST_INTERVAL."""
        async with self._mektep_request_time_lock:
            current_time_mono = time.monotonic()
            elapsed_since_last = current_time_mono - self._last_mektep_request_time
            if elapsed_since_last < self.cfg.MEKTEP_REQUEST_INTERVAL:
                await asyncio.sleep(self.cfg.MEKTEP_REQUEST_INTERVAL - elapsed_since_last)
            self._last_mektep_request_time = time.monotonic()

    def _sync_do_login(self) -> bool:
        if self.session is None:
            self.session = requests.Session()
            retry_strategy = Retry(
                total=3, 
                backoff_factor=1, 
                status_forcelist=[429, 500, 502, 503, 504],
                allowed_methods=["HEAD", "GET", "POST"]
            )
            adapter = HTTPAdapter(pool_connections=30, pool_maxsize=30, max_retries=retry_strategy)
            self.session.mount('http://', adapter)
            self.session.mount('https://', adapter)
            
            current_headers = self.BASE_HEADERS.copy()
            current_headers["Origin"] = self.login_url_base
            self.session.headers.update(current_headers)
        
        self.log.info(f"[HTTP Fetcher] Attempting login to {self.cfg.LOGIN_URL}...")
        try:
            r0 = self.session.get(self.cfg.LOGIN_URL, timeout=30)
            r0.raise_for_status()
        except requests.exceptions.Timeout as e:
            self.log.error(f"[HTTP Fetcher] Timeout getting login page: {e}"); return False
        except requests.exceptions.ConnectionError as e:
            self.log.error(f"[HTTP Fetcher] Connection error getting login page: {e}"); return False
        except requests.RequestException as e:
            self.log.error(f"[HTTP Fetcher] Error getting login page: {e}"); return False

        soup = BeautifulSoup(r0.text, "html.parser")
        form = soup.find("form", {"id": "login_form"}) or soup.find("form")
        if not form: self.log.error("[HTTP Fetcher] Login form not found."); return False

        login_data = { inp["name"]: inp.get("value", "") for inp in form.find_all("input", {"type": "hidden"}) if inp.get("name") }
        login_data["usr_login"] = self.cfg.USERNAME
        login_data["usr_password"] = self.cfg.PASSWORD        
        action_url_part = form.get("action") or ""
        post_url = urljoin(self.cfg.LOGIN_URL, action_url_part)

        login_headers = self.session.headers.copy()
        login_headers["Referer"] = self.cfg.LOGIN_URL

        try:
            r1 = self.session.post(post_url, data=login_data, headers=login_headers, timeout=30, allow_redirects=True)
            r1.raise_for_status()
            if "office" in r1.url.lower() or self.cfg.USERNAME in r1.text or "profile" in r1.text.lower() or "Мой кабинет" in r1.text:
                self.log.info("[HTTP Fetcher] Login POST successful, attempting office page validation.")
                r_office = self.session.get(self.office_url, headers={"Referer": r1.url}, timeout=20)
                if r_office.status_code == 200 and ("profile" in r_office.text.lower() or "Мои классы" in r_office.text):
                     self.log.info("[HTTP Fetcher] Office page confirmed. Login successful."); self._is_logged_in = True; return True
                else: self.log.warning(f"[HTTP Fetcher] Office page validation failed (status {r_office.status_code}). Login might be partial."); return False
            else: self.log.error(f"[HTTP Fetcher] Login failed. URL: {r1.url}. Status: {r1.status_code}."); return False
        except requests.exceptions.Timeout as e:
            self.log.error(f"[HTTP Fetcher] Timeout during login POST: {e}"); return False
        except requests.exceptions.ConnectionError as e:
            self.log.error(f"[HTTP Fetcher] Connection error during login POST: {e}"); return False
        except requests.RequestException as e: 
            self.log.error(f"[HTTP Fetcher] Error during login POST: {e}"); return False

    async def login(self) -> bool:
        async with self._login_lock:
            if self._is_logged_in: return True
            self._is_logged_in = False 
            return await self._run_sync(self._sync_do_login)

    def _sync_call_endpoint(self, endpoint_name: str, params: dict, referer_url: str) -> Tuple[Optional[dict], Optional[str]]:
        if not self.session or not self._is_logged_in:
            self.log.error(f"[HTTP Fetcher] No active/valid session for calling endpoint {endpoint_name}.")
            return None, "session_error"

        target_url = f"{self.ajax_url_base}?r={endpoint_name}"
        ajax_headers = self.session.headers.copy()
        ajax_headers["Referer"] = referer_url
        ajax_headers["Content-Type"] = "application/x-www-form-urlencoded; charset=UTF-8"

        try:
            r = self.session.post(target_url, data=params, headers=ajax_headers, timeout=20)
            r.raise_for_status()
            text = r.text.strip()

            if not text or text.lower() == "false":
                if endpoint_name == "get-predmet-info": self.log.warning(f"[DEBUG] {endpoint_name} returned empty or 'false'.")
                # считаем это не ошибкой API, а спецификой ответа (может быть предмета нет)
                return None, None

            json_response = r.json()
            return json_response, None

        except requests.exceptions.JSONDecodeError:
            self.log.warning(f"[HTTP Fetcher] Endpoint {endpoint_name} response is not JSON. Status: {r.status_code if 'r' in locals() else 'N/A'}. Response: {text[:200] if 'text' in locals() else 'N/A'}")
            if 'r' in locals() and r.status_code in [401, 403]:
                 self.log.info("[HTTP Fetcher] Auth error suspected on non-JSON response, marking as logged out.")
                 self._is_logged_in = False
            return None, "json_error"
        except requests.exceptions.Timeout as e:
            self.log.error(f"[HTTP Fetcher] Timeout calling endpoint {endpoint_name}: {e}")
            return None, "timeout"
        except requests.exceptions.ConnectionError as e:
            self.log.error(f"[HTTP Fetcher] Connection error calling endpoint {endpoint_name}: {e}. Marking as logged out.")
            self._is_logged_in = False
            return None, "connection_error"
        except requests.RequestException as e:
            self.log.error(f"[HTTP Fetcher] Error calling endpoint {endpoint_name}: {e}")
            if hasattr(e, 'response') and e.response is not None:
                if e.response.status_code in [401, 403]:
                    self.log.info("[HTTP Fetcher] Auth error, marking as logged out.")
                    self._is_logged_in = False
                return None, f"http_error_{e.response.status_code}"
            else:
                self.log.info("[HTTP Fetcher] RequestException without response, likely network issue. Marking as logged out.")
                self._is_logged_in = False
                return None, "request_exception"
        except Exception as e:
            self.log.error(f"[HTTP Fetcher] Unexpected error in _sync_call_endpoint for {endpoint_name}: {type(e).__name__} - {e}")
            self.log.exception(e)
            self._is_logged_in = False
            return None, "unexpected_error"

    async def call_endpoint(self, endpoint_name: str, params: dict, referer_url: str) -> Optional[dict]:
        async with self._stats_lock:
            self.total_api_calls += 1

        if not self._is_logged_in:
            self.log.info(f"[HTTP Fetcher] Not logged in before calling {endpoint_name}. Attempting to login.")
            if not await self.login():
                self.log.error(f"[HTTP Fetcher] Login failed, cannot call {endpoint_name}.")
                async with self._stats_lock:
                    self.api_errors += 1
                return None

        if not self._is_logged_in:
            self.log.error(f"[HTTP Fetcher] Still not logged in after login attempt. Cannot call {endpoint_name}.")
            async with self._stats_lock:
                self.api_errors += 1
            return None

        async with self._mektep_semaphore:
            await self._ensure_request_interval()

            class_id_log = params.get('classId', 'N/A')
            class_predmet_id_log = params.get('classPredmetId', 'N/A')
            selected_quarter_log = params.get('selectedQuarter', 'N/A')
            
            self.log.info(
                f"[HTTP Fetcher] Calling endpoint: '{endpoint_name}'. "
                f"ClassID: {class_id_log}, PredmetID: {class_predmet_id_log}, Q: {selected_quarter_log}, "
                f"Timestamp: {time.time():.2f}"
            )
            
            result, error_type = await self._run_sync(self._sync_call_endpoint, endpoint_name, params, referer_url)
            if error_type:
                async with self._stats_lock:
                    self.api_errors += 1
                    if error_type == "timeout":
                        self.api_timeouts += 1
        
        return result
    
    async def get_api_stats(self) -> Dict[str, int]:
        """Возвращает словарь со статистикой вызовов API."""
        async with self._stats_lock:
            return {
                "total_calls": self.total_api_calls,
                "total_errors": self.api_errors,
                "timeouts": self.api_timeouts,
            }

    async def fetch_subject_data(self, class_id: str, class_predmet_id: str, quarters_to_fetch: Optional[Iterable[int]] = None) -> Tuple[Optional[Dict[str, Any]], bool]:
        if quarters_to_fetch is None:
            quarters_to_fetch = [self.cfg.CURRENT_MONITORING_QUARTER]
        if not self._is_logged_in:
            self.log.info(f"[HTTP Fetcher] Not logged in before fetching data for {class_id}/{class_predmet_id}. Attempting login.")
            if not await self.login():
                self.log.error(f"[HTTP Fetcher] Login failed before fetching data for {class_id}/{class_predmet_id}.")
                return None, True 
        if not self._is_logged_in:
             self.log.error(f"[HTTP Fetcher] Still not logged in after login attempt. Cannot fetch data for {class_id}/{class_predmet_id}.")
             return None, True

        mektep_id, current_year = self.cfg.MEKTEP_ID, self.cfg.CURRENT_YEAR
        subject_data_container: Dict[str, Any] = {
            "subject_details": {"original_class_id": class_id, "original_class_predmet_id": class_predmet_id}, 
            "students_grades": {}
        }
        referer = f"{self.office_url}?action=predmets&class={class_id}&predmet={class_predmet_id}"
        get_predmet_info_call_failed = False 
        js_predmet_info = await self.call_endpoint("get-predmet-info", {"mektepId": mektep_id, "classPredmetId": class_predmet_id, "currentYear": current_year}, referer)
        predmet_info_api = None
        teacher_id_from_api = None
        
        if js_predmet_info and isinstance(js_predmet_info.get("info"), dict):
            predmet_info_api = js_predmet_info["info"]
            subject_data_container["subject_details"].update({
                k: predmet_info_api.get(k) for k in ["classId", "classNumber", "classLetter", "predmetId", "predmetName", "teacherId", "teacherFio"]
            })
            teacher_id_from_api = predmet_info_api.get("teacherId") 
            subject_data_container["subject_details"]["teacher_id"] = teacher_id_from_api 
            
            subject_data_container["subject_details"]["max_scores_by_quarter"] = {}
            if isinstance(predmet_info_api.get("predmetSochSorMax"), dict):
                 for q_str, scores_list in predmet_info_api["predmetSochSorMax"].items():
                    soch_max, sor_max_list = None, []
                    if isinstance(scores_list, list) and scores_list:
                        soch_max_str = str(scores_list[0]).strip()
                        if soch_max_str.isdigit(): soch_max = int(soch_max_str)
                        elif soch_max_str and soch_max_str.lower() != 'none': soch_max = scores_list[0]
                        sor_max_list = [int(s) if str(s).strip().isdigit() else (str(s).strip() if str(s).strip() and str(s).strip().lower() != 'none' else None) for s in scores_list[1:]]
                        sor_max_list = [s for s in sor_max_list if s is not None]
                    subject_data_container["subject_details"]["max_scores_by_quarter"][q_str] = {"soch_max": soch_max, "sor_max": sor_max_list}
        else:
            if not get_predmet_info_call_failed:
                 self.log.warning(f"[HTTP Fetcher] get-predmet-info was invalid (not None, but wrong structure) for {class_id}/{class_predmet_id}.")
            get_predmet_info_call_failed = True
            subject_data_container["subject_details"]["teacher_id"] = None

        teacher_id_to_use = subject_data_container["subject_details"].get("teacher_id")

        if not teacher_id_to_use and get_predmet_info_call_failed:
             self.log.warning(f"[HTTP Fetcher] Teacher ID is missing due to get-predmet-info failure for subject {class_id}/{class_predmet_id} BEFORE quarter loop. SOR/SOCH data will be incomplete.")
        elif not teacher_id_to_use:
             self.log.info(f"[HTTP Fetcher] Teacher ID is None for subject {class_id}/{class_predmet_id} (get-predmet-info call status: {'failed' if get_predmet_info_call_failed else 'ok'}). SOR/SOCH data might be incomplete.")
        
        subgroup, subgroupId = (predmet_info_api.get("subgroup", 0), predmet_info_api.get("subgroupId", 0)) if predmet_info_api else (0,0)
        
        js_students = await self.call_endpoint("get-students-list", {"mektepId": mektep_id, "classId": class_id, "classPredmetId": class_predmet_id, "subgroup": subgroup, "subgroupId": subgroupId, "selectedQuarter": 1, "currentYear": current_year}, referer)
        if js_students is None:
            self.log.error(f"[HTTP Fetcher] get-students-list call failed (returned None) for {class_id}/{class_predmet_id}. Student list will be empty.")
        elif not isinstance(js_students.get("allStudents"), dict):
            self.log.error(f"[HTTP Fetcher] get-students-list returned invalid data structure for {class_id}/{class_predmet_id}. Student list will be empty.")
        else:
            for sid, s_info in js_students["allStudents"].items():
                if isinstance(s_info, dict) and "id" in s_info:
                    subject_data_container["students_grades"][s_info["id"]] = {"fio": s_info.get("fio"), "fio_full": s_info.get("fio_full"), "quarters": {str(q): {"formative_assessments": [], "summative_assessments_for_section": [], "summative_assessment_for_term": None, "quarter_final_mark": None} for q in range(1,5)}}
        
        js_tabel = await self.call_endpoint("get-tabel-makrs", {"mektepId": mektep_id, "classId": class_id, "classPredmetId": class_predmet_id, "selectedQuarter": 1, "currentYear": current_year}, referer)
        if js_tabel and isinstance(js_tabel.get("quarterMarks"), dict):
            for q_str, s_q_marks in js_tabel["quarterMarks"].items():
                if isinstance(s_q_marks, dict):
                    for sid_t, q_mark in s_q_marks.items():
                        if sid_t in subject_data_container["students_grades"]: subject_data_container["students_grades"][sid_t]["quarters"][q_str]["quarter_final_mark"] = str(q_mark).strip() or None
        elif js_tabel is None:
            self.log.warning(f"[HTTP Fetcher] get-tabel-makrs call failed (returned None) for {class_id}/{class_predmet_id}.")

        for quarter_num in quarters_to_fetch:
            q_str_loop = str(quarter_num)
            
            grades_payload = {"mektepId": mektep_id, "classId": class_id, "classPredmetId": class_predmet_id, "selectedQuarter": quarter_num, "currentYear": current_year}
            js_journal_grades = await self.call_endpoint("get-journal-grades", grades_payload, referer)
            if js_journal_grades and isinstance(js_journal_grades.get("jurnalGrades"), dict):
                 for date_key, lessons in js_journal_grades["jurnalGrades"].items():
                    if isinstance(lessons, dict):
                        for lesson_period, s_marks_lesson in lessons.items(): 
                            if isinstance(s_marks_lesson, dict):
                                for sid_g, m_details in s_marks_lesson.items():
                                    if sid_g in subject_data_container["students_grades"] and isinstance(m_details, dict) and "mark" in m_details:
                                        mark_val = str(m_details["mark"]).strip()
                                        if mark_val: subject_data_container["students_grades"][sid_g]["quarters"][q_str_loop]["formative_assessments"].append({"id": m_details.get("id"), "date": date_key, "lesson_period": lesson_period, "mark": int(mark_val) if mark_val.isdigit() else mark_val})
            elif js_journal_grades is None:
                 self.log.warning(f"[HTTP Fetcher] get-journal-grades call failed (returned None) for Q{q_str_loop} of {class_id}/{class_predmet_id}.")

            if not teacher_id_to_use:
                if get_predmet_info_call_failed: 
                    self.log.warning(f"[HTTP Fetcher] Skipping SOR/SOCH for Q{q_str_loop} of {class_id}/{class_predmet_id} because teacher_id is missing due to get-predmet-info failure.")
                continue 

            sor_payload = {"mektepId": mektep_id, "classId": class_id, "classPredmetId": class_predmet_id, "selectedQuarter": quarter_num, "currentYear": current_year, "teacherId": teacher_id_to_use}
            js_sor_marks = await self.call_endpoint("get-journal-sor-makrs", sor_payload, referer)
            
            if js_sor_marks is None:
                self.log.warning(f"[HTTP Fetcher] get-journal-sor-makrs call failed (returned None) for Q{q_str_loop} of {class_id}/{class_predmet_id}.")
            
            max_scores_for_q = subject_data_container["subject_details"]["max_scores_by_quarter"].get(q_str_loop, {})
            max_soch_q_val, max_sors_q_list_val = max_scores_for_q.get("soch_max"), max_scores_for_q.get("sor_max", []) 
            sor_marks_data_from_api = js_sor_marks.get("sorMarks") if js_sor_marks else None

            if isinstance(sor_marks_data_from_api, dict) and sor_marks_data_from_api:
                for sor_key_api, student_marks_dict in sor_marks_data_from_api.items():
                    if not isinstance(student_marks_dict, dict): continue
                    for student_id_sor, sor_mark_val_any in student_marks_dict.items():
                        sor_mark_val_str = str(sor_mark_val_any).strip()
                        if not sor_mark_val_str or student_id_sor not in subject_data_container["students_grades"]: continue
                        current_q_data = subject_data_container["students_grades"][student_id_sor]["quarters"][q_str_loop]
                        if sor_key_api == "0": 
                            current_q_data["summative_assessment_for_term"] = {"mark": int(sor_mark_val_str) if sor_mark_val_str.isdigit() else sor_mark_val_str, "max_mark": max_soch_q_val }
                        else: 
                            try:
                                sor_num_api = int(sor_key_api) 
                                current_sor_max_mark = max_sors_q_list_val[sor_num_api - 1] if 1 <= sor_num_api <= len(max_sors_q_list_val) else None
                                current_q_data["summative_assessments_for_section"].append({ "sor_number": sor_num_api, "mark": int(sor_mark_val_str) if sor_mark_val_str.isdigit() else sor_mark_val_str, "max_mark": current_sor_max_mark })
                            except (ValueError, IndexError): self.log.warning(f"Error parsing SOR num/max for key {sor_key_api}, student {student_id_sor}, Q{q_str_loop}")
            elif isinstance(sor_marks_data_from_api, list) and sor_marks_data_from_api:
                 for index, student_marks_dict_item in enumerate(sor_marks_data_from_api):
                    if not isinstance(student_marks_dict_item, dict): continue
                    for student_id_sor, sor_mark_val_any in student_marks_dict_item.items():
                        sor_mark_val_str = str(sor_mark_val_any).strip()
                        if not sor_mark_val_str or student_id_sor not in subject_data_container["students_grades"]: continue
                        current_q_data = subject_data_container["students_grades"][student_id_sor]["quarters"][q_str_loop]
                        if index == 0: 
                            current_q_data["summative_assessment_for_term"] = {"mark": int(sor_mark_val_str) if sor_mark_val_str.isdigit() else sor_mark_val_str, "max_mark": max_soch_q_val}
                        else: 
                            sor_num_list_based = index 
                            current_sor_max_mark = max_sors_q_list_val[sor_num_list_based - 1] if 1 <= sor_num_list_based <= len(max_sors_q_list_val) else None
                            current_q_data["summative_assessments_for_section"].append({"sor_number": sor_num_list_based, "mark": int(sor_mark_val_str) if sor_mark_val_str.isdigit() else sor_mark_val_str, "max_mark": current_sor_max_mark})

        if not subject_data_container["subject_details"].get("teacher_id") and get_predmet_info_call_failed:
             self.log.warning(f"[HTTP Fetcher] Final check: Teacher ID is missing for subject {class_id}/{class_predmet_id} due to get-predmet-info failure. SOR/SOCH data likely incomplete.")
        
        return subject_data_container, get_predmet_info_call_failed

    async def close_session(self):
        if self.session:
            await self._run_sync(self.session.close)
            self.log.info("[HTTP Fetcher] Session closed.")
            self.session = None
            self._is_logged_in = False

HTTP_FETCHER: Optional[AsyncHTTPDataFetcher] = None

# ───────────────────────────────────────────────────────────────────────────────
# 4. SQLITE DATABASE
# ───────────────────────────────────────────────────────────────────────────────
class SQLDB:
    def __init__(self, db_name: str, config_obj: Config):
        self.db_path = db_name
        self.config_obj = config_obj 
        self.conn: Optional[sqlite3.Connection] = None
        self.lock = asyncio.Lock() 

        self.users: Dict[int, Dict[str, Any]] = {}
        self.enabled: bool = True
        self.students: Dict[str, List[str]] = {} 
        self.grades: Dict[str, Dict] = {} 

        self._connect_db()
        self._initialize_db()
        self._load_all_data_from_db() 
        LOGGER.info(f"[SQLDB] Initialization complete. Users: {len(self.users)}, Students: {len(self.students)}, Grades: {len(self.grades)}, Enabled: {self.enabled}")

    def _connect_db(self):
        try:
            self.conn = sqlite3.connect(self.db_path, check_same_thread=False)
            self.conn.row_factory = sqlite3.Row 
            LOGGER.info(f"[SQLDB] Connected to SQLite database: {self.db_path}")
        except sqlite3.Error as e:
            LOGGER.critical(f"[SQLDB] CRITICAL: Error connecting to SQLite database: {e}")
            self.conn = None
            raise 

    def _initialize_db(self):
        if not self.conn:
            LOGGER.critical("[SQLDB] CRITICAL: Cannot initialize DB, no connection.")
            return
        try:
            with self.conn:
                self.conn.execute("""
                    CREATE TABLE IF NOT EXISTS configuration (
                        key TEXT PRIMARY KEY,
                        value TEXT NOT NULL
                    )
                """)
                self.conn.execute("""
                    CREATE TABLE IF NOT EXISTS users (
                        chat_id INTEGER PRIMARY KEY,
                        user_data TEXT NOT NULL
                    )
                """)
                self.conn.execute("""
                    CREATE TABLE IF NOT EXISTS application_state (
                        key TEXT PRIMARY KEY,
                        value TEXT NOT NULL
                    )
                """)
                self.conn.execute("""
                    CREATE TABLE IF NOT EXISTS student_lists (
                        class_name TEXT PRIMARY KEY,
                        students_json TEXT NOT NULL
                    )
                """)
                self.conn.execute("""
                    CREATE TABLE IF NOT EXISTS grade_snapshots (
                        url TEXT PRIMARY KEY,
                        snapshot_data_json TEXT NOT NULL
                    )
                """)
            LOGGER.info("[SQLDB] Database tables initialized/verified.")
            self._populate_default_config_db()
        except sqlite3.Error as e:
            LOGGER.critical(f"[SQLDB] CRITICAL: Error initializing database tables: {e}")

    def _populate_default_config_db(self):
        if not self.conn: return
        
        # Use default values from the Config class instance passed at __init__
        defaults = {
            "LOGIN_URL": self.config_obj.DEFAULT_LOGIN_URL,
            "USERNAME": self.config_obj.DEFAULT_USERNAME,
            "PASSWORD": self.config_obj.DEFAULT_PASSWORD,
            "MEKTEP_ID": self.config_obj.DEFAULT_MEKTEP_ID,
            "CURRENT_YEAR": self.config_obj.DEFAULT_CURRENT_YEAR,
            "CURRENT_MONITORING_QUARTER": str(self.config_obj.DEFAULT_CURRENT_MONITORING_QUARTER),
            "CLASS_SUBJECT_SITES": json.dumps(self.config_obj.DEFAULT_CLASS_SUBJECT_SITES, ensure_ascii=False),
            "CLASS_STUDENTS_URLS": json.dumps(self.config_obj.DEFAULT_CLASS_STUDENTS_URLS, ensure_ascii=False),
        }
        try:
            with self.conn:
                for key, value in defaults.items():
                    self.conn.execute(
                        "INSERT OR IGNORE INTO configuration (key, value) VALUES (?, ?)",
                        (key, value)
                    )
            LOGGER.info("[SQLDB] Default configuration values populated in DB (if missing).")
        except sqlite3.Error as e:
            LOGGER.error(f"[SQLDB] Error populating default configuration in DB: {e}")

    def load_config_into_object(self, target_config_obj: Config):
        """Populates the provided Config object with in-code defaults only."""
        defaults = self.config_obj

        target_config_obj.LOGIN_URL = defaults.DEFAULT_LOGIN_URL
        target_config_obj.USERNAME = defaults.DEFAULT_USERNAME
        target_config_obj.PASSWORD = defaults.DEFAULT_PASSWORD
        target_config_obj.MEKTEP_ID = defaults.DEFAULT_MEKTEP_ID
        target_config_obj.CURRENT_YEAR = defaults.DEFAULT_CURRENT_YEAR
        target_config_obj.CURRENT_MONITORING_QUARTER = defaults.DEFAULT_CURRENT_MONITORING_QUARTER
        target_config_obj.CLASS_SUBJECT_SITES = defaults.DEFAULT_CLASS_SUBJECT_SITES
        target_config_obj.CLASS_STUDENTS_URLS = defaults.DEFAULT_CLASS_STUDENTS_URLS

        LOGGER.info("[SQLDB] Configuration populated from Config defaults (DB overrides disabled).")

    def _load_all_data_from_db(self):
        if not self.conn: 
            LOGGER.error("[SQLDB] Cannot load data, no DB connection.")
            return
        try:
            loaded_users = {}
            for row in self.conn.execute("SELECT chat_id, user_data FROM users"):
                try:
                    chat_id_val = int(row['chat_id'])
                    loaded_users[chat_id_val] = json.loads(row['user_data'])
                except json.JSONDecodeError as e:
                    LOGGER.error(f"[SQLDB] Failed to parse user_data for chat_id {row['chat_id']}: {e}")
                except ValueError:
                    LOGGER.error(f"[SQLDB] Invalid chat_id format from DB: {row['chat_id']}")
            self.users = loaded_users

            state_row = self.conn.execute("SELECT value FROM application_state WHERE key = 'enabled'").fetchone()
            self.enabled = state_row['value'] == 'true' if state_row else True 

            loaded_students = {}
            for row in self.conn.execute("SELECT class_name, students_json FROM student_lists"):
                try:
                    loaded_students[row['class_name']] = json.loads(row['students_json'])
                except json.JSONDecodeError as e:
                    LOGGER.error(f"[SQLDB] Failed to parse students_json for class_name {row['class_name']}: {e}")
            self.students = loaded_students

            loaded_grades = {}
            for row in self.conn.execute("SELECT url, snapshot_data_json FROM grade_snapshots"):
                try:
                    loaded_grades[row['url']] = json.loads(row['snapshot_data_json'])
                except json.JSONDecodeError as e:
                    LOGGER.error(f"[SQLDB] Failed to parse snapshot_data_json for url {row['url']}: {e}")
            self.grades = loaded_grades
            
        except sqlite3.Error as e:
            LOGGER.error(f"[SQLDB] Error loading data collections (users, state, students, grades) from SQLite: {e}")

    async def save_all_data_to_db(self):
        if not self.conn:
            LOGGER.error("[SQLDB] Cannot save data to DB, no connection.")
            return
        
        try:
            with self.conn:
                for chat_id, data in self.users.items():
                    self.conn.execute(
                        "INSERT OR REPLACE INTO users (chat_id, user_data) VALUES (?, ?)",
                        (chat_id, json.dumps(data, ensure_ascii=False))
                    )
                
                self.conn.execute(
                    "INSERT OR REPLACE INTO application_state (key, value) VALUES (?, ?)",
                    ('enabled', 'true' if self.enabled else 'false')
                )

                for class_name, student_list in self.students.items():
                    self.conn.execute(
                        "INSERT OR REPLACE INTO student_lists (class_name, students_json) VALUES (?, ?)",
                        (class_name, json.dumps(student_list, ensure_ascii=False))
                    )

                for url, grade_data in self.grades.items():
                    self.conn.execute(
                        "INSERT OR REPLACE INTO grade_snapshots (url, snapshot_data_json) VALUES (?, ?)",
                        (url, json.dumps(grade_data, ensure_ascii=False))
                    )
        except sqlite3.Error as e:
            LOGGER.error(f"[SQLDB] Error saving data collections to SQLite: {e}")
        except json.JSONDecodeError:
            LOGGER.error(f"[SQLDB] JSON encoding error while saving data to SQLite.")

    async def delete_user(self, chat_id: int) -> str:
        """
        Remove user both from in-memory cache and the SQLite store.
        Returns status string: 'success', 'not_found', or 'error'.
        """
        if not self.conn:
            LOGGER.error("[SQLDB] Cannot delete user, no DB connection.")
            return "error"

        async with self.lock:
            cached_user = self.users.pop(chat_id, None)
            deleted_from_db = False

            try:
                with self.conn:
                    cursor = self.conn.execute(
                        "DELETE FROM users WHERE chat_id = ?",
                        (chat_id,)
                    )
                    deleted_from_db = cursor.rowcount > 0
            except sqlite3.Error as e:
                LOGGER.error(f"[SQLDB] Error deleting user {chat_id} from SQLite: {e}")
                if cached_user is not None:
                    self.users[chat_id] = cached_user
                return "error"

            if cached_user is None and not deleted_from_db:
                return "not_found"
            return "success"

    def _populate_students_from_live_data(self, all_live_sgs_data: Dict[str, Dict[str, Any]]):
        sgs_students_by_class_name = defaultdict(set)
        if not all_live_sgs_data: LOGGER.warning("[SQLDB] No live SGS data for student list population."); return

        try:
            class_students_urls = self.config_obj.CLASS_STUDENTS_URLS 

            for class_id_sgs_str_key, subjects_in_class_sgs in all_live_sgs_data.items():
                class_name_sgs = None
                for cn, curl in class_students_urls.items():
                    parsed_cid, _ = parse_url_to_get_ids(curl)
                    if str(parsed_cid) == str(class_id_sgs_str_key): class_name_sgs = cn; break
                
                if class_name_sgs:
                    for subject_data_sgs in subjects_in_class_sgs.values():
                        if 'students_grades' in subject_data_sgs:
                            for student_info_sgs in subject_data_sgs['students_grades'].values():
                                if 'fio' in student_info_sgs: sgs_students_by_class_name[class_name_sgs].add(student_info_sgs['fio'])
                            break 
            
            self.students = {cls: sorted(list(names)) for cls, names in sgs_students_by_class_name.items()}
            LOGGER.info(f"[SQLDB] Populated/updated student lists from live data for {len(self.students)} classes.")
            
        except Exception as e: LOGGER.error(f"[SQLDB] Error populating students from live data: {e}"); LOGGER.exception(e)


    def close_db(self):
        if self.conn:
            try:
                self.conn.close()
                LOGGER.info("[SQLDB] SQLite database connection closed.")
            except sqlite3.Error as e:
                LOGGER.error(f"[SQLDB] Error closing SQLite database connection: {e}")
        self.conn = None

DS: Optional[SQLDB] = None

# ───────────────────────────────────────────────────────────────────────────────
# 5. UTILITY FUNCTIONS FOR DIFF
# ───────────────────────────────────────────────────────────────────────────────
def calculate_fo_average(fo_list: List[Dict]) -> Optional[str]:
    numeric_marks = []
    for fo in fo_list:
        mark = fo.get("mark")
        if isinstance(mark, (int, float)):
            numeric_marks.append(mark)
        elif isinstance(mark, str):
            try:
                numeric_marks.append(float(mark.replace(',', '.')))
            except ValueError:
                pass 
    if not numeric_marks:
        return None
    
    avg = sum(numeric_marks) / len(numeric_marks)
    if avg == int(avg):
        return str(int(avg))
    else:
        return f"{avg:.1f}" 

def compare_native_data(old_subject_data: Optional[Dict], new_subject_data: Optional[Dict]) -> Dict[str, Dict[str, Dict]]:
    changes: Dict[str, Dict[str, Dict]] = defaultdict(lambda: defaultdict(dict))
    old_students = old_subject_data.get("students_grades", {}) if old_subject_data else {}
    new_students = new_subject_data.get("students_grades", {}) if new_subject_data else {}
    all_student_ids = set(old_students.keys()) | set(new_students.keys())

    for student_id in all_student_ids:
        old_s_data = old_students.get(student_id)
        new_s_data = new_students.get(student_id)
        student_fio = (new_s_data or old_s_data or {}).get("fio", f"ID_{student_id}")
        old_quarters = (old_s_data or {}).get("quarters", {})
        new_quarters = (new_s_data or {}).get("quarters", {})
        all_quarters = set(old_quarters.keys()) | set(new_quarters.keys())

        for q_str in all_quarters:
            q_changes: Dict[str, Any] = defaultdict(list)
            old_q_data = old_quarters.get(q_str, {})
            new_q_data = new_quarters.get(q_str, {})

            old_fo_numeric = []
            old_attendance = []
            for item in old_q_data.get("formative_assessments", []):
                mark = item.get("mark")
                if isinstance(mark, (int, float)) or (isinstance(mark, str) and mark.isdigit()):
                    old_fo_numeric.append(item)
                elif isinstance(mark, str) and mark.strip():
                    old_attendance.append(item)
            
            new_fo_numeric = []
            new_attendance = []
            for item in new_q_data.get("formative_assessments", []):
                mark = item.get("mark")
                if isinstance(mark, (int, float)) or (isinstance(mark, str) and mark.isdigit()):
                    new_fo_numeric.append(item)
                elif isinstance(mark, str) and mark.strip():
                    new_attendance.append(item)

            old_fo_avg = calculate_fo_average(old_fo_numeric)
            new_fo_avg = calculate_fo_average(new_fo_numeric)
            
            old_fo_num_set = set(tuple(sorted(fo.items())) for fo in old_fo_numeric)
            new_fo_num_set = set(tuple(sorted(fo.items())) for fo in new_fo_numeric)
            added_fo_num = [dict(fo_tuple) for fo_tuple in new_fo_num_set - old_fo_num_set]
            removed_fo_num = [dict(fo_tuple) for fo_tuple in old_fo_num_set - new_fo_num_set]
            
            if added_fo_num: q_changes["formative_added"] = added_fo_num
            if removed_fo_num: q_changes["formative_removed"] = removed_fo_num
            if added_fo_num or removed_fo_num or (old_fo_avg != new_fo_avg):
                if old_fo_avg is not None:
                    q_changes["formative_avg_old"] = old_fo_avg
                if new_fo_avg is not None:
                    q_changes["formative_avg_new"] = new_fo_avg

            old_att_set = set(tuple(sorted(att.items())) for att in old_attendance)
            new_att_set = set(tuple(sorted(att.items())) for att in new_attendance)
            added_att = [dict(att_tuple) for att_tuple in new_att_set - old_att_set]
            removed_att = [dict(att_tuple) for att_tuple in old_att_set - new_att_set]

            if added_att: q_changes["attendance_added"] = added_att
            if removed_att: q_changes["attendance_removed"] = removed_att

            old_sors = {sor["sor_number"]: sor for sor in old_q_data.get("summative_assessments_for_section", []) if "sor_number" in sor}
            new_sors = {sor["sor_number"]: sor for sor in new_q_data.get("summative_assessments_for_section", []) if "sor_number" in sor}
            for sor_num, new_sor_data in new_sors.items():
                old_sor_data = old_sors.get(sor_num)
                if not old_sor_data: q_changes["sor_added"].append(new_sor_data)
                elif old_sor_data.get("mark") != new_sor_data.get("mark"):
                     q_changes["sor_changed"].append({"sor_number": sor_num, "old_mark": old_sor_data.get("mark"), "new_mark": new_sor_data.get("mark"), "max_mark": new_sor_data.get("max_mark")})
            for sor_num, old_sor_data in old_sors.items():
                if sor_num not in new_sors: q_changes["sor_removed"].append(old_sor_data)
                
            old_soch = old_q_data.get("summative_assessment_for_term"); new_soch = new_q_data.get("summative_assessment_for_term")
            if new_soch and not old_soch: q_changes["soch_added"] = new_soch
            elif not new_soch and old_soch: q_changes["soch_removed"] = old_soch
            elif new_soch and old_soch and old_soch.get("mark") != new_soch.get("mark"):
                 q_changes["soch_changed"] = {"old_mark": old_soch.get("mark"),"new_mark": new_soch.get("mark"),"max_mark": new_soch.get("max_mark")}

            old_final = old_q_data.get("quarter_final_mark"); new_final = new_q_data.get("quarter_final_mark")
            if str(old_final) != str(new_final):
                if new_final is not None and str(new_final).strip() != "": q_changes["final_mark_changed"] = {"old": old_final, "new": new_final}
                elif old_final is not None and str(old_final).strip() != "": q_changes["final_mark_removed"] = {"old": old_final}

            if q_changes:
                changes[student_fio][q_str] = dict(q_changes)
                
    return dict(changes)

def format_hms(sec: float) -> str:
    h = int(sec // 3600); sec %= 3600
    m = int(sec // 60); s = int(sec % 60)
    return f"{h:02d}:{m:02d}:{s:02d}"

# ───────────────────────────────────────────────────────────────────────────────
# 6. TELEGRAM BOT
# ───────────────────────────────────────────────────────────────────────────────
class TelegramBot:
    def __init__(self, cfg: Config, ds: SQLDB, log: Logger, bot: Bot, message_queue: MessageQueue):
        self.cfg = cfg
        self.ds = ds
        self.log = log
        self.bot = bot
        self.mq = message_queue
        self._teacher_digest_task = asyncio.create_task(self._teacher_digest_scheduler())

    async def _teacher_digest_scheduler(self) -> None:
        while True:
            try:
                await self._process_teacher_digests()
            except Exception as e:
                self.log.error(f"[TeacherDigest] Ошибка при обработке ежедневной рассылки: {e}")
            await asyncio.sleep(60)

    async def _process_teacher_digests(self) -> None:
        now = datetime.now()
        today_str = now.strftime("%Y-%m-%d")
        current_minutes = now.hour * 60 + now.minute
        data_changed = False

        for user_id, user_info in list(self.ds.users.items()):
            if user_info.get("user_mode") != "teacher":
                continue
            time_str = user_info.get("teacher_daily_time") or self.cfg.DEFAULT_TEACHER_DIGEST_TIME
            assigned_default_time = False
            if not user_info.get("teacher_daily_time"):
                user_info["teacher_daily_time"] = time_str
                data_changed = True
                assigned_default_time = True
            try:
                hour_str, minute_str = time_str.split(":", 1)
                hour_val = int(hour_str)
                minute_val = int(minute_str)
            except (ValueError, AttributeError):
                continue
            target_minutes = hour_val * 60 + minute_val
            if assigned_default_time and not user_info.get("teacher_last_digest_date") and current_minutes >= target_minutes:
                user_info["teacher_last_digest_date"] = today_str
                data_changed = True
            last_sent = user_info.get("teacher_last_digest_date")
            pending_list = user_info.get("teacher_pending_notifications") or []
            if current_minutes >= target_minutes and last_sent != today_str:
                if pending_list:
                    digest_header = f"Ежедневное уведомление ({now.strftime('%d.%m.%Y')})"
                    digest_body = self._build_teacher_digest_body(pending_list)
                    final_message = f"{digest_header}\n\n{digest_body}" if digest_body else digest_header
                    await self.send_long(user_id, final_message)
                    user_info["teacher_pending_notifications"] = []
                    self.log.info(f"[TeacherDigest] Отправлена ежедневная рассылка учителю {user_id}.")
                    user_info["teacher_last_digest_date"] = today_str
                    data_changed = True
                else:
                    await self.send_long(user_id, f"Ежедневная ({now.strftime('%d.%m.%Y')}) сводка по вашему классу: изменений нет.")
                    self.log.info(f"[TeacherDigest] Изменений для учителя {user_id} нет, отправлено уведомление без изменений.")
                    user_info["teacher_last_digest_date"] = today_str
                    data_changed = True

        if data_changed:
            await self.ds.save_all_data_to_db()

    async def send_resources_analysis(self, chat_id: int):

        current_time_for_analysis = time.time()

        uptime_seconds = current_time_for_analysis - START_TIME + UPTIME_OFFSET
        uptime_formatted = format_hms(uptime_seconds)

        monitor_status = "Включен" if self.ds.enabled else "Выключен"

        process = psutil.Process(os.getpid())
        cpu_usage = process.cpu_percent(interval=0.1)
        memory_info = process.memory_info()
        memory_rss_mb = memory_info.rss / (1024 * 1024)
        memory_vms_mb = memory_info.vms / (1024 * 1024)
        try:
            db_dir = os.path.dirname(os.path.abspath(self.ds.db_path))
            disk_usage = psutil.disk_usage(db_dir)
            disk_free_gb = disk_usage.free / (1024 * 1024 * 1024)
            disk_total_gb = disk_usage.total / (1024 * 1024 * 1024)
            disk_percent_used = disk_usage.percent
            disk_path_display = os.path.basename(db_dir) 
        except Exception: 
            disk_free_gb, disk_total_gb, disk_percent_used, disk_path_display = 'Err', 'Err', 'Err', 'Err'

        db_size_mb = 0
        users_count_db = 0
        grades_count_db = 0
        if self.ds.conn:
             try:
                 db_size_bytes = os.path.getsize(self.ds.db_path)
                 db_size_mb = db_size_bytes / (1024 * 1024)
                 users_count_db = len(self.ds.users)
                 grades_count_db = len(self.ds.grades)
             except Exception:
                 db_size_mb = 'Err'

        current_quarter = self.cfg.CURRENT_MONITORING_QUARTER
        num_classes_cfg = len(self.cfg.CLASS_SUBJECT_SITES)
        num_subjects_cfg = sum(len(subjects) for subjects in self.cfg.CLASS_SUBJECT_SITES.values())

        total_tasks = 0
        min_interval_val = 0
        max_interval_val = 0
        avg_interval_val = 0
        intervals_at_min = 0
        intervals_at_max = 0
        last_success_times_ago = []
        tasks_never_succeeded = 0
        active_monitor_tasks = []

        if GRADES_MONITOR_INSTANCE and hasattr(GRADES_MONITOR_INSTANCE, 'subject_tasks_meta'):
            active_monitor_tasks = [
                task_info.get('task_obj')
                for group in GRADES_MONITOR_INSTANCE.subject_tasks_meta.values()
                for task_info in group
                if task_info.get('task_obj')
                   and hasattr(task_info['task_obj'], 'current_interval')
                   and hasattr(task_info['task_obj'], 'last_success_time')
            ]
            total_tasks = len(active_monitor_tasks)

            if active_monitor_tasks:
                task_intervals = [task.current_interval for task in active_monitor_tasks]
                min_interval_val = GRADES_MONITOR_INSTANCE.min_interval
                max_interval_val = self.cfg.CHECK_INTERVAL
                try:
                    avg_interval_val = statistics.mean(task_intervals) if task_intervals else 0
                    intervals_at_min = sum(1 for i in task_intervals if abs(i - min_interval_val) < 1)
                    intervals_at_max = sum(1 for i in task_intervals if abs(i - max_interval_val) < 1)
                except statistics.StatisticsError: pass

                for task in active_monitor_tasks:
                    if task.last_success_time:
                        last_success_times_ago.append(current_time_for_analysis - task.last_success_time)
                    else:
                        tasks_never_succeeded += 1

        min_ago_str, max_ago_str, avg_ago_str = "N/A", "N/A", "N/A"
        if last_success_times_ago:
            min_ago = min(last_success_times_ago)
            max_ago = max(last_success_times_ago)
            avg_ago = statistics.mean(last_success_times_ago)
            min_ago_str = format_hms(min_ago)
            max_ago_str = format_hms(max_ago)
            avg_ago_str = format_hms(avg_ago)

        fetcher_logged_in = "Да" if HTTP_FETCHER._is_logged_in else "Нет"
        fetcher_limit = self.cfg.MEKTEP_CONCURRENT_REQUEST_LIMIT
        fetcher_available_slots = HTTP_FETCHER._mektep_semaphore._value if hasattr(HTTP_FETCHER._mektep_semaphore, '_value') else 'N/A'
        fetcher_used_slots = f"{fetcher_limit - fetcher_available_slots}/{fetcher_limit}" if isinstance(fetcher_available_slots, int) else 'N/A'
        api_stats = await HTTP_FETCHER.get_api_stats()

        mq_size = MESSAGE_SENDER_QUEUE.get_queue_size()
        mq_worker_status = MESSAGE_SENDER_QUEUE.get_worker_status()
        tg_send_errors = await MESSAGE_SENDER_QUEUE.get_telegram_error_count() 

        teacher_id_failures = GRADES_MONITOR_INSTANCE.consecutive_teacher_id_failures if GRADES_MONITOR_INSTANCE else 'N/A'
        max_failures = self.cfg.MAX_CONSECUTIVE_TEACHER_ID_FAILURES

        analysis_text = (
            f" <b>Анализ ресурсов и загруженности</b> ({datetime.now().strftime('%Y-%m-%d %H:%M:%S')}) \n\n"
            f" <b>Аптайм бота:</b> {uptime_formatted}\n"
            f" <b>Статус мониторинга:</b> {monitor_status}\n\n"

            f" <b>Системные ресурсы:</b>\n"
            f"  - CPU Usage: {cpu_usage:.1f} %\n"
            f"  - Memory (RSS/VMS): {memory_rss_mb:.1f} MB / {memory_vms_mb:.1f} MB\n"
            f"  - Disk Free/Total ({disk_path_display}): {disk_free_gb:.1f} GB / {disk_total_gb:.1f} GB ({disk_percent_used} % used)\n\n"

            f" <b>База данных ({os.path.basename(self.ds.db_path)}):</b>\n"
            f"  - Размер файла: {db_size_mb:.2f} MB\n"
            f"  - Пользователей: {users_count_db}\n"
            f"  - Снимков оценок: {grades_count_db}\n\n"

            f" <b>Конфигурация Мониторинга:</b>\n"
            f"  - Текущая четверть: {current_quarter}\n"
            f"  - Классов настроено: {num_classes_cfg}\n"
            f"  - Предметов настроено: {num_subjects_cfg}\n\n"

            f" <b>Задачи мониторинга ({total_tasks} шт.):</b>\n"
            f"  - Интервалы (сек): Мин/Макс/Сред: {min_interval_val:.1f}/{max_interval_val:.1f}/{avg_interval_val:.1f}\n"
            f"  - Задач на Мин/Макс интервале: {intervals_at_min} / {intervals_at_max}\n"
            f"  - Время с последнего <u>успеха</u> (Мин/Макс/Сред): {min_ago_str} / {max_ago_str} / {avg_ago_str}\n"
            f"  - Задач без успеха: {tasks_never_succeeded}\n\n"

            f" <b>HTTP Fetcher (Mektep):</b>\n"
            f"  - Статус логина: {fetcher_logged_in}\n"
            f"  - Исп./Лимит запросов: {fetcher_used_slots}\n"
            f"  - Всего API вызовов: {api_stats['total_calls']}\n"
            f"  - Всего API ошибок: {api_stats['total_errors']}\n"
            f"  - API таймаутов: {api_stats['timeouts']}\n\n"

            f" <b>Очередь сообщений Telegram:</b>\n"
            f"  - Сообщений в очереди: {mq_size}\n"
            f"  - Статус обработчика: {mq_worker_status}\n"
            f"  - Ошибок отправки TG: {tg_send_errors}\n\n"

            f" <b>Счетчик крит. сбоев (TeacherID):</b> {teacher_id_failures} / {max_failures}"
        )

        await self.send_long(chat_id, analysis_text)

    async def _shutdown_resources(self, graceful_queue_shutdown: bool = True, save_data: bool = True):
        """helper method to gracefully shut down resources."""
        self.log.info(f"Initiating resource shutdown (graceful_queue: {graceful_queue_shutdown}, save_data: {save_data})...")
        
        global MESSAGE_SENDER_QUEUE, HTTP_FETCHER, DS

        if MESSAGE_SENDER_QUEUE:
            self.log.info("Stopping message sender queue...")
            await MESSAGE_SENDER_QUEUE.stop(process_queue=graceful_queue_shutdown)
        
        if HTTP_FETCHER:
            self.log.info("Closing HTTP fetcher session...")
            await HTTP_FETCHER.close_session()
        
        if DS:
            if save_data:
                self.log.info("Saving data to SQLDB...")
                await DS.save_all_data_to_db()
            self.log.info("Closing SQLDB connection...")
            DS.close_db()
        
        self.log.info("Resource shutdown complete.")

    async def execute_restart(self, reason: str):
        """handles the /restart command logic."""
        self.log.info(f"RESTART command triggered by admin. Reason: {reason}")
        await self.send(self.cfg.ADMIN_CHAT_ID, f"Перезапуск бота...\n<b>Причина:</b> {reason}")
        
        await self._shutdown_resources(graceful_queue_shutdown=True, save_data=True)
        
        self.log.info("Attempting to stop the current event loop for restart...")
        try:
            loop = asyncio.get_running_loop()
            loop.stop()
        except RuntimeError:
            self.log.warning("No running event loop to stop for restart, or already stopping.")
        except Exception as e_loop_stop:
            self.log.error(f"Error stopping event loop for restart: {e_loop_stop}")

        self.log.info(f"Executing restart: {sys.executable} {' '.join(sys.argv)}")
        try:
            os.execl(sys.executable, sys.executable, *sys.argv)
        except Exception as e_execl:
            self.log.critical(f"CRITICAL: os.execl failed during admin restart: {e_execl}. Bot will exit.")
            sys.exit(1)

    async def execute_stop(self, initiated_by_user_id: int):
        """handles the /stop command logic."""
        self.log.info(f"STOP command triggered by user {initiated_by_user_id}.")
        await self.send(initiated_by_user_id, "Полная остановка бота...")
        if initiated_by_user_id != self.cfg.ADMIN_CHAT_ID:
            await self.send(self.cfg.ADMIN_CHAT_ID, f"Бот остановлен пользователем {initiated_by_user_id}.")
            
        await self._shutdown_resources(graceful_queue_shutdown=True, save_data=True)
        
        self.log.info("Attempting to stop the current event loop for full stop...")
        try:
            loop = asyncio.get_running_loop()
            loop.stop()
        except RuntimeError:
            self.log.warning("No running event loop to stop for full stop, or already stopping.")
        except Exception as e_loop_stop:
            self.log.error(f"Error stopping event loop for full stop: {e_loop_stop}")
        self.log.info("Bot stop sequence initiated. Event loop should terminate.")
        sys.exit(0)

    async def execute_fast_stop(self, initiated_by_user_id: int):
        """
        handles the /fast_stop command logic.
        the goal here is to leave the process immediately
        """
        self.log.warning(f"HARD FAST_STOP requested by {initiated_by_user_id}. "
                         "The process will exit with os._exit(0) right now.")

        try:
            await self.bot.send_message(
                initiated_by_user_id,
                "Бот завершается немедленно! (Может не успеть доставить это сообщение.)")
        except Exception:
            pass

        try:
            sys.stdout.flush()
            sys.stderr.flush()
        except Exception:
            pass

        os._exit(0)

    async def send(self, chat_id: int, text: str):
        if not text: return
        await self.mq.add_to_queue(chat_id, text, message_type="send", parse_mode=enums.ParseMode.HTML)

    TAG_SYNONYMS = {
        "strong": "b", "em": "i", "ins": "u",
        "strike": "s", "del": "s",
    }
    STACKABLE_TAGS = {"b", "i", "u", "s", "code", "pre", "tg-spoiler"}

    def _escape_html(self, text: str) -> str:
        """Экранирует специальные HTML-символы в строке."""
        if not text:
            return ""
        return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")

    async def send_long(
        self,
        chat_id: int,
        text: str,
        max_length: int = 4000,
    ):

        if not text:
            self.log.warning(f"[send_long] empty text for chat {chat_id}")
            return

        try:
            splitter = _SafeTelegramSplitter(text, max_length)
            parts = splitter.parts
        except Exception as exc:
            self.log.error(f"[send_long] HTML parse failed: {exc}. Falling back.")
            # very conservative fallback – escape everything, split blindly
            esc = escape(text)
            parts = [
                esc[i : i + max_length] for i in range(0, len(esc), max_length)
            ]

        for idx, part in enumerate(parts, 1):
            if not part.strip():
                continue
            self.log.info(
                f"[send_long] sending chunk {idx}/{len(parts)}, len={len(part)}"
            )
            try:
                await self.mq.add_to_queue(
                    chat_id,
                    part,
                    message_type="send",
                    parse_mode=enums.ParseMode.HTML,
                )
            except Exception as e:
                self.log.warning(f"Telegram rejected chunk {idx}: {e}")
                self.log.debug(f"Offending chunk:\n{part}")
            if idx < len(parts):
                await asyncio.sleep(0.02)

    async def broadcast(self, text: str):
        if not text: return
        user_ids = list(self.ds.users.keys())
        self.log.info(f"[Broadcast] Queuing message for {len(user_ids)} users.")
        for uid in user_ids:
            await self.mq.add_to_queue(uid, text, message_type="send", parse_mode=enums.ParseMode.HTML)
            await asyncio.sleep(0.02)

    async def send_kb(self, chat_id: int, text: str, keys: List[List[Dict[str, str]]]):
        if not text: return
        kb = types.InlineKeyboardMarkup(inline_keyboard=keys)
        await self.mq.add_to_queue(chat_id, text, message_type="send_kb", reply_markup=kb, parse_mode=enums.ParseMode.HTML)

    def _student_class(self, student: str) -> str:
        for cls, studs in self.ds.students.items():
            if student in studs:
                return cls
        return ""

    def _normalize_class_name(self, value: Optional[str]) -> str:
        if not value or not isinstance(value, str):
            return ""
        cleaned = value.strip().upper()
        for token in ("КЛАСС", "КЛ.", "CLASS", "CL.", "CLS", "КЛ"):
            cleaned = cleaned.replace(token, "")
        cleaned = re.sub(r"\s+", "", cleaned)
        for ch in ('"', "'", "`", "’", "‘", "-", "_", ".", ",", "(", ")", "[", "]", "{", "}", "№", "#", "/"):
            cleaned = cleaned.replace(ch, "")
        cleaned = cleaned.translate(CLASS_NAME_LATIN_TO_CYRILLIC)
        return cleaned

    async def notify_structured_changes(self, subject_info: Dict[str, Any], structured_changes: Dict[str, Dict[str, Dict]]):
        if not structured_changes:
            return

        subject_display_name = subject_info.get("subject_display_name", "?Предмет?")
        class_name = subject_info.get("class_name", "?Класс?") 
        subject_name_for_message = subject_display_name

        months_map = {
            1: 'января', 2: 'февраля', 3: 'марта', 4: 'апреля',
            5: 'мая', 6: 'июня', 7: 'июля', 8: 'августа',
            9: 'сентября', 10: 'октября', 11: 'ноября', 12: 'декабря'
        }
        notifications_per_user: Dict[int, List[str]] = defaultdict(list)
        teacher_notifications_modified = False

        for student_fio, quarters_changes in structured_changes.items():
            student_actual_class = self._student_class(student_fio) or class_name
            personal_messages_for_this_student_subject: List[str] = []
            detailed_changes_for_pg_bullet_list: List[str] = []

            for q_str, q_changes in quarters_changes.items():
                pg_attendance_added_details_list = []
                personal_attendance_added_details_list = []
                if q_changes.get("attendance_added"):
                    for att in q_changes["attendance_added"]:
                        mark_date_str_att = att.get('date', 'не указана')
                        formatted_date_att = mark_date_str_att
                        try:
                            if mark_date_str_att != 'не указана':
                                date_obj = datetime.strptime(mark_date_str_att, '%Y-%m-%d')
                                formatted_date_att = f"{date_obj.day} {months_map[date_obj.month]}"
                        except (ValueError, KeyError): pass
                        personal_attendance_added_details_list.append(f"«{att.get('mark', '?')}» за {formatted_date_att}")
                        pg_attendance_added_details_list.append(f"«{att.get('mark', '?')}»({att.get('date', '')})")
                if personal_attendance_added_details_list:
                    verb_att = "Выставлена" if len(personal_attendance_added_details_list) == 1 else "Выставлены"
                    noun_att = "отметка о посещении" if len(personal_attendance_added_details_list) == 1 else "отметки о посещении"
                    details_str = ", ".join(personal_attendance_added_details_list)
                    personal_messages_for_this_student_subject.append(f"{verb_att} {noun_att}: {details_str} по предмету «{subject_name_for_message}».")
                if pg_attendance_added_details_list:
                     detailed_changes_for_pg_bullet_list.append(f"Отмечено посещение: {', '.join(pg_attendance_added_details_list)}")

                pg_attendance_removed_details_list = []
                personal_attendance_removed_details_list = []
                if q_changes.get("attendance_removed"):
                    for att in q_changes["attendance_removed"]:
                        mark_date_str_att = att.get('date', 'не указана')
                        formatted_date_att = mark_date_str_att
                        try:
                            if mark_date_str_att != 'не указана':
                                date_obj = datetime.strptime(mark_date_str_att, '%Y-%m-%d')
                                formatted_date_att = f"{date_obj.day} {months_map[date_obj.month]}"
                        except (ValueError, KeyError): pass
                        personal_attendance_removed_details_list.append(f"«{att.get('mark', '?')}» за «{formatted_date_att}»")
                        pg_attendance_removed_details_list.append(f"«{att.get('mark', '?')}»({att.get('date', '')})")
                if personal_attendance_removed_details_list:
                    verb_att = "Убрана" if len(personal_attendance_removed_details_list) == 1 else "Убраны"
                    noun_att = "отметка о посещении" if len(personal_attendance_removed_details_list) == 1 else "отметки о посещении"
                    details_str = ", ".join(personal_attendance_removed_details_list)
                    personal_messages_for_this_student_subject.append(f"{verb_att} {noun_att}: {details_str} по предмету «{subject_name_for_message}».")
                if pg_attendance_removed_details_list:
                    detailed_changes_for_pg_bullet_list.append(f"Убрана отметка посещения: {', '.join(pg_attendance_removed_details_list)}")

                fo_actions_personal = []
                pg_fo_actions_for_bullet = []
                added_fo_item_details_list_personal = []
                pg_added_fo_details_list_pg = []
                if q_changes.get("formative_added"):
                    for fm in q_changes["formative_added"]:
                        mark_value_fo = fm.get('mark', '?')
                        mark_date_str_fo = fm.get('date', 'не указана')
                        formatted_mark_date_fo = mark_date_str_fo
                        if mark_date_str_fo != 'не указана':
                            try:
                                mark_date_obj_fo = datetime.strptime(mark_date_str_fo, '%Y-%m-%d')
                                formatted_mark_date_fo = f"{mark_date_obj_fo.day} {months_map[mark_date_obj_fo.month]}"
                            except (ValueError, KeyError): pass
                        added_fo_item_details_list_personal.append(f"<b>«{mark_value_fo}»</b> за {formatted_mark_date_fo}")
                        pg_added_fo_details_list_pg.append(f"<b>«{mark_value_fo}»</b>({fm.get('date', '')})")
                if added_fo_item_details_list_personal:
                    verb = "Выставлено" if len(added_fo_item_details_list_personal) == 1 else "Выставлены"; noun = "ФО" 
                    fo_actions_personal.append(f"{verb} {noun}: {', '.join(added_fo_item_details_list_personal)}")
                if pg_added_fo_details_list_pg:
                    verb_pg = "Выставлено" if len(pg_added_fo_details_list_pg) == 1 else "Выставлены"
                    pg_fo_actions_for_bullet.append(f"{verb_pg} ФО: {', '.join(pg_added_fo_details_list_pg)}")

                removed_fo_item_details_list_personal = []
                pg_removed_fo_details_list_pg = []
                if q_changes.get("formative_removed"):
                    for fm in q_changes["formative_removed"]:
                        mark_value_fo = fm.get('mark', '?')
                        mark_date_str_fo = fm.get('date', 'не указана')
                        formatted_mark_date_fo = mark_date_str_fo
                        if mark_date_str_fo != 'не указана':
                            try:
                                mark_date_obj_fo = datetime.strptime(mark_date_str_fo, '%Y-%m-%d')
                                formatted_mark_date_fo = f"{mark_date_obj_fo.day} {months_map[mark_date_obj_fo.month]}"
                            except (ValueError, KeyError): pass
                        removed_fo_item_details_list_personal.append(f"<b>«{mark_value_fo}»</b> за {formatted_mark_date_fo}")
                        pg_removed_fo_details_list_pg.append(f"<b>«{mark_value_fo}»</b>({fm.get('date', '')})")
                if removed_fo_item_details_list_personal:
                    verb = "Удален" if len(removed_fo_item_details_list_personal) == 1 else "Удалены"; noun = "ФО"
                    fo_actions_personal.append(f"{verb} {noun}: {', '.join(removed_fo_item_details_list_personal)}")
                if pg_removed_fo_details_list_pg:
                    verb_pg = "Удален" if len(pg_removed_fo_details_list_pg) == 1 else "Удалены"
                    pg_fo_actions_for_bullet.append(f"{verb_pg} ФО: {', '.join(pg_removed_fo_details_list_pg)}")
                
                if fo_actions_personal:
                    main_fo_text = ". ".join(fo_actions_personal)
                    final_fo_message_personal = f"{main_fo_text} по предмету «{subject_name_for_message}»."
                    avg_change_sentence_fo = ""
                    if added_fo_item_details_list_personal or removed_fo_item_details_list_personal:
                        new_fo_average = q_changes.get("formative_avg_new"); old_fo_average = q_changes.get("formative_avg_old")
                        if new_fo_average is not None or old_fo_average is not None:
                            if old_fo_average is None and new_fo_average is not None: avg_change_sentence_fo = f"Впервые среднее ФО <b>«{new_fo_average}»</b>."
                            elif old_fo_average is not None and new_fo_average is None: avg_change_sentence_fo = f"Ранее среднее ФО было «{old_fo_average}», теперь ФО нет."
                            elif old_fo_average != new_fo_average and new_fo_average is not None: avg_change_sentence_fo = f"Среднее ФО изменилось с «{old_fo_average}» на <b>«{new_fo_average}»</b>."
                    if avg_change_sentence_fo: final_fo_message_personal += f" {avg_change_sentence_fo}"
                    personal_messages_for_this_student_subject.append(final_fo_message_personal)
                if pg_fo_actions_for_bullet: detailed_changes_for_pg_bullet_list.append(". ".join(pg_fo_actions_for_bullet))

                sor_actions_personal = []; pg_sor_actions_for_bullet = []
                added_sor_details_list_personal = []; pg_added_sor_details_list_pg = []
                if q_changes.get("sor_added"):
                    for s_item in q_changes["sor_added"]:
                        detail = f"№{s_item['sor_number']} <b>«{s_item.get('mark','?')}/{s_item.get('max_mark','?')}»</b>"
                        added_sor_details_list_personal.append(detail); pg_added_sor_details_list_pg.append(detail)
                if added_sor_details_list_personal:
                    verb = "Выставлен" if len(added_sor_details_list_personal) == 1 else "Выставлены"
                    sor_actions_personal.append(f"{verb} СОР: {', '.join(added_sor_details_list_personal)}")
                if pg_added_sor_details_list_pg:
                    verb_pg = "Выставлен" if len(pg_added_sor_details_list_pg) == 1 else "Выставлены"
                    pg_sor_actions_for_bullet.append(f"{verb_pg} СОР: {', '.join(pg_added_sor_details_list_pg)}")

                changed_sor_details_list_personal = []; pg_changed_sor_details_list_pg = []
                if q_changes.get("sor_changed"):
                    for s_item in q_changes["sor_changed"]:
                        detail = f"№{s_item['sor_number']} с «{s_item.get('old_mark','?')}/{s_item.get('max_mark','?')}» на <b>«{s_item.get('new_mark','?')}/{s_item.get('max_mark','?')}»</b>"
                        changed_sor_details_list_personal.append(detail); pg_changed_sor_details_list_pg.append(detail)
                if changed_sor_details_list_personal:
                    verb = "Изменен" if len(changed_sor_details_list_personal) == 1 else "Изменены"
                    sor_actions_personal.append(f"{verb} СОР: {', '.join(changed_sor_details_list_personal)}")
                if pg_changed_sor_details_list_pg:
                    verb_pg = "Изменен" if len(pg_changed_sor_details_list_pg) == 1 else "Изменены"
                    pg_sor_actions_for_bullet.append(f"{verb_pg} СОР: {', '.join(pg_changed_sor_details_list_pg)}")
                
                removed_sor_details_list_personal = []; pg_removed_sor_details_list_pg = []
                if q_changes.get("sor_removed"):
                    for s_item in q_changes["sor_removed"]:
                        detail = f"№{s_item['sor_number']} <b>«{s_item.get('mark','?')}/{s_item.get('max_mark','?')}»</b>"
                        removed_sor_details_list_personal.append(detail); pg_removed_sor_details_list_pg.append(detail)
                if removed_sor_details_list_personal:
                    verb = "Удален" if len(removed_sor_details_list_personal) == 1 else "Удалены"
                    sor_actions_personal.append(f"{verb} СОР: {', '.join(removed_sor_details_list_personal)}")
                if pg_removed_sor_details_list_pg:
                    verb_pg = "Удален" if len(pg_removed_sor_details_list_pg) == 1 else "Удалены"
                    pg_sor_actions_for_bullet.append(f"{verb_pg} СОР: {', '.join(pg_removed_sor_details_list_pg)}")

                if sor_actions_personal:
                    personal_messages_for_this_student_subject.append(f"{'. '.join(sor_actions_personal)} по предмету «{subject_name_for_message}».")
                if pg_sor_actions_for_bullet: detailed_changes_for_pg_bullet_list.append(". ".join(pg_sor_actions_for_bullet))
                
                soch_action_description_personal = ""; pg_soch_bullet = ""
                if q_changes.get("soch_added"):
                    s_item = q_changes["soch_added"]
                    soch_action_description_personal = f"Выставлен СОЧ: <b>«{s_item.get('mark','?')}/{s_item.get('max_mark','?')}»</b>"
                    pg_soch_bullet = f"Выставлен СОЧ: <b>«{s_item.get('mark','?')}/{s_item.get('max_mark','?')}»</b>"
                elif q_changes.get("soch_changed"):
                    s_item = q_changes["soch_changed"]
                    soch_action_description_personal = f"Изменен СОЧ: с «{s_item.get('old_mark','?')}/{s_item.get('max_mark','?')}» на <b>«{s_item.get('new_mark','?')}/{s_item.get('max_mark','?')}»</b>"
                    pg_soch_bullet = f" Изменен СОЧ: «{s_item.get('old_mark','?')}/{s_item.get('max_mark','?')}» → <b>«{s_item.get('new_mark','?')}/{s_item.get('max_mark','?')}»</b>"
                elif q_changes.get("soch_removed"):
                    s_item = q_changes["soch_removed"]
                    soch_action_description_personal = f"Удален СОЧ: <b>«{s_item.get('mark','?')}/{s_item.get('max_mark','?')}»</b>"
                    pg_soch_bullet = f"Удален СОЧ: <b>«{s_item.get('mark','?')}/{s_item.get('max_mark','?')}»</b>"
                if soch_action_description_personal:
                    personal_messages_for_this_student_subject.append(f"{soch_action_description_personal} по предмету «{subject_name_for_message}».")
                if pg_soch_bullet: detailed_changes_for_pg_bullet_list.append(pg_soch_bullet)
                
                final_mark_action_description_personal = ""; pg_final_mark_bullet = ""
                if q_changes.get("final_mark_changed"):
                    fc = q_changes["final_mark_changed"]
                    final_mark_action_description_personal = f"Изменена итоговая оценка: на <b>«{fc.get('new','?')}»</b> (была «{fc.get('old','?')}»)"
                    pg_final_mark_bullet = f" Изменена итоговая оценка: «{fc.get('old','?')}» → <b>«{fc.get('new','?')}»</b>"
                elif q_changes.get("final_mark_removed"):
                    fc = q_changes["final_mark_removed"]
                    final_mark_action_description_personal = f"Удалена итоговая оценка (была <b>«{fc.get('old','?')}»</b>)"
                    pg_final_mark_bullet = f"Удалена итоговая оценка (была <b>«{fc.get('old','?')}»</b>)"
                if final_mark_action_description_personal:
                    personal_messages_for_this_student_subject.append(f"{final_mark_action_description_personal} по предмету «{subject_name_for_message}».")
                if pg_final_mark_bullet: detailed_changes_for_pg_bullet_list.append(pg_final_mark_bullet)

            if personal_messages_for_this_student_subject:
                for user_id_loop, user_info_loop in list(self.ds.users.items()):
                    mode = user_info_loop.get("user_mode")
                    if mode == "personal" and user_info_loop.get("student") == student_fio:
                        notifications_per_user[user_id_loop].extend(personal_messages_for_this_student_subject)
            
            if detailed_changes_for_pg_bullet_list:
                content_for_pg_message = "\n".join(f" {change_item}" for change_item in detailed_changes_for_pg_bullet_list if change_item.strip())
                if content_for_pg_message.strip():
                    pg_subject_header = f"По предмету «<b>{subject_display_name}</b>» ({class_name}):\n"
                    final_pg_message_content = pg_subject_header + content_for_pg_message
                    teacher_entry_payload = {
                        "student": student_fio,
                        "class": student_actual_class,
                        "subject": subject_display_name,
                        "details": content_for_pg_message,
                    }
                    for user_id_loop, user_info_loop in list(self.ds.users.items()):
                        mode = user_info_loop.get("user_mode")
                        student_class_norm = self._normalize_class_name(student_actual_class)
                        if mode == "partial":
                            user_classes_raw = user_info_loop.get("classes", [])
                            if isinstance(user_classes_raw, (list, tuple, set)):
                                class_matches = any(
                                    self._normalize_class_name(cls_item) == student_class_norm
                                    for cls_item in user_classes_raw
                                    if isinstance(cls_item, str)
                                )
                            elif isinstance(user_classes_raw, str):
                                class_matches = self._normalize_class_name(user_classes_raw) == student_class_norm
                            else:
                                class_matches = False
                            if class_matches:
                                notifications_per_user[user_id_loop].append(f" <b>{student_fio}</b> ({student_actual_class}):\n" + final_pg_message_content)
                        elif mode == "global":
                            notifications_per_user[user_id_loop].append(f" <b>{student_fio}</b> ({student_actual_class}):\n" + final_pg_message_content)
                        elif mode == "teacher":
                            teacher_classes = user_info_loop.get("classes")
                            teacher_class = user_info_loop.get("class")
                            matches_class = False
                            teacher_candidates: List[str] = []
                            if isinstance(teacher_classes, (list, tuple, set)):
                                teacher_candidates.extend(
                                    cls_item for cls_item in teacher_classes if isinstance(cls_item, str)
                                )
                            elif isinstance(teacher_classes, str) and teacher_classes:
                                teacher_candidates.append(teacher_classes)
                            if isinstance(teacher_class, str) and teacher_class:
                                teacher_candidates.append(teacher_class)
                            for candidate in teacher_candidates:
                                if self._normalize_class_name(candidate) == student_class_norm:
                                    matches_class = True
                                    break
                            if matches_class:
                                pending_list = user_info_loop.setdefault("teacher_pending_notifications", [])
                                pending_list.append(dict(teacher_entry_payload))
                                teacher_notifications_modified = True

        if teacher_notifications_modified:
            await self.ds.save_all_data_to_db()

        for user_id, messages_to_send_list in notifications_per_user.items():
            if messages_to_send_list:
                is_personal_mode = self.ds.users.get(user_id, {}).get("user_mode") == "personal"
                if is_personal_mode:
                    for individual_msg_item in messages_to_send_list:
                        await self.send_long(user_id, individual_msg_item) 
                else: 
                    final_text_to_send_pg = "\n\n".join(messages_to_send_list) 
                    await self.send_long(user_id, final_text_to_send_pg)

    def _build_teacher_digest_body(self, pending_items: List[Any]) -> str:
        if not pending_items:
            return ""

        structured: Dict[str, Dict[str, List[Any]]] = {}
        legacy_chunks: List[str] = []

        for item in pending_items:
            if isinstance(item, dict):
                student = str(item.get("student", "")).strip()
                subject = str(item.get("subject", "")).strip()
                details = item.get("details")
                if not student or not subject or details is None:
                    legacy_chunks.append(str(item))
                    continue
                subjects_bucket = structured.setdefault(student, {})
                subjects_bucket.setdefault(subject, []).append(details)
            else:
                legacy_chunks.append(str(item))

        digest_blocks: List[str] = []
        for student, subjects in structured.items():
            block_lines: List[str] = [f"-<b>{student}</b>:"]
            for subject, details_list in subjects.items():
                detail_lines: List[str] = []
                seen_lines: set[str] = set()
                for details in details_list:
                    if isinstance(details, (list, tuple)):
                        candidate_lines: List[str] = []
                        for detail_item in details:
                            candidate_lines.extend(str(detail_item).splitlines())
                    else:
                        candidate_lines = str(details).splitlines()
                    for raw_line in candidate_lines:
                        stripped_line = raw_line.strip()
                        if not stripped_line or stripped_line in seen_lines:
                            continue
                        seen_lines.add(stripped_line)
                        detail_lines.append(f"    {stripped_line}")
                if detail_lines:
                    block_lines.append(f"--<b>{subject}</b>:")
                    block_lines.extend(detail_lines)
            if len(block_lines) > 1:
                digest_blocks.append("\n".join(block_lines))

        digest_blocks.extend(chunk for chunk in legacy_chunks if str(chunk).strip())
        return "\n\n".join(digest_blocks)

    async def get_student_absences(self, student_fio: str, student_class: Optional[str]) -> str:
            if not student_class:
                return "Не удалось определить класс для запроса пропусков."

            all_absences = []
            total_absence_count = 0
            subjects_for_class = self.cfg.CLASS_SUBJECT_SITES.get(student_class, {})
            if not subjects_for_class:
                return f"На данный момент для класса {student_class} не настроены отслеживаемые предметы."

            for subject_name, url in subjects_for_class.items():
                sgs_entry = self.ds.grades.get(url)
                if not sgs_entry or not sgs_entry.get("students_grades"):
                    continue
                student_snapshot = None
                for s_data in sgs_entry["students_grades"].values():
                    if s_data.get("fio") == student_fio:
                        student_snapshot = s_data
                        break
                if not student_snapshot or not student_snapshot.get("quarters"):
                    continue
                for q_data in student_snapshot["quarters"].values():
                    for fo in q_data.get("formative_assessments", []):
                        mark = fo.get("mark")
                        date_str = fo.get("date", "0000-00-00")
                        if isinstance(mark, str) and not mark.isdigit() and mark.strip(): # считаем нецифровые строки пропусками
                            all_absences.append((date_str, subject_name, mark.strip()))
                            total_absence_count += 1
            
            all_absences.sort(key=lambda x: x[0])

            header = f"<b>Пропуски для {student_fio} ({student_class}) за учебный год:</b>"
            if not all_absences:
                return f"{header}\n\nНа данный момент у вас нет ни одного пропуска."

            report_lines = [header]
            
            count_unique_days_with_absences = 0

            for date_str, group in groupby(all_absences, key=lambda x: x[0]):
                count_unique_days_with_absences += 1
                report_lines.append("")
                report_lines.append(f"<u>{date_str}:</u>")
                absences_on_this_day = []
                for _, subj, mk in group:
                    absences_on_this_day.append(f"  - {subj}: <b>{mk}</b>")
                report_lines.extend(absences_on_this_day)
            
            report_lines.append("")
            report_lines.append(f"<b>Всего дней с пропусками: {count_unique_days_with_absences}</b>")
            report_lines.append(f"<b>Всего пропущенных уроков: {total_absence_count}</b>")
            
            absence_counts = Counter(mark for _, _, mark in all_absences)
            reason_groups = {
                "без уважительной причины": ["ж", "н"], "по уважительной причине": ["д", "п"],
                "по болезни": ["а", "б"], "освобождение": ["бос", "осв"]
            }
            report_lines.append("")
            report_lines.append("<b>Сводка по причинам пропусков:</b>")
            used_codes = set()
            for reason, codes in reason_groups.items():
                cnt = sum(absence_counts.get(code, 0) for code in codes)
                if cnt: 
                    report_lines.append(f"- {reason}: {cnt}")
                    used_codes.update(codes)
            
            others_text = []
            for code, cnt in sorted(absence_counts.items()):
                if code not in used_codes and cnt > 0:
                    others_text.append(f"  • «{code}»: {cnt}")
            
            if others_text:
                report_lines.append("- прочие отметки (неклассифицированные пропуски):")
                report_lines.extend(others_text)
                
            return "\n".join(report_lines)

    async def get_student_formatives(self, student_fio: str, student_class: Optional[str]) -> str:
        if not student_class:
            return "Не удалось определить класс для запроса формативных оценок."

        formatives_by_subject_quarter: Dict[str, Dict[str, List[Any]]] = defaultdict(lambda: defaultdict(list))
        subjects_for_class_config = self.cfg.CLASS_SUBJECT_SITES.get(student_class, {})
        if not subjects_for_class_config:
            return f"Для класса {student_class} не настроены предметы для отслеживания."

        for subject_display_name, url in subjects_for_class_config.items():
            sgs_entry = self.ds.grades.get(url)
            if sgs_entry and sgs_entry.get("students_grades"):
                student_data = None
                for s_id, s_data_iter in sgs_entry["students_grades"].items():
                    if s_data_iter.get("fio") == student_fio:
                        student_data = s_data_iter; break
                if student_data and student_data.get("quarters"):
                    for q_str, q_data in student_data["quarters"].items():
                        for fo_item in q_data.get("formative_assessments", []):
                            mark = fo_item.get("mark"); is_numeric = False; numeric_value = None
                            if isinstance(mark, (int, float)): is_numeric = True; numeric_value = mark
                            elif isinstance(mark, str):
                                try: numeric_value = float(mark.replace(',', '.')); is_numeric = True
                                except ValueError: pass
                            if is_numeric:
                                formatives_by_subject_quarter[subject_display_name][q_str].append(numeric_value)
        report_lines = [f"<b>Формативные оценки для {student_fio} ({student_class}):</b>"]
        found_any_formatives = False
        sorted_subjects = sorted(formatives_by_subject_quarter.keys())
        for subject_name in sorted_subjects:
            subject_has_marks = False
            subject_lines = [f"\n<u>{subject_name}:</u>"]
            quarters_data = formatives_by_subject_quarter[subject_name]
            sorted_quarters = sorted(quarters_data.keys())
            for q_str in sorted_quarters:
                marks_list = quarters_data[q_str]
                if marks_list:
                    subject_has_marks = True; found_any_formatives = True
                    marks_str_list = [str(int(m)) if isinstance(m, (float, int)) and m == int(m) else str(m) for m in marks_list]
                    fo_items_for_avg = [{"mark": m} for m in marks_list]
                    average_str = calculate_fo_average(fo_items_for_avg)
                    avg_display = f" (Среднее: {average_str})" if average_str is not None else ""
                    subject_lines.append(f"- Четверть {q_str}: {', '.join(marks_str_list)}{avg_display}")
            if subject_has_marks: report_lines.extend(subject_lines)
        if not found_any_formatives:
            report_lines.append("\nНа данный момент у вас нет ни одного ФО.")
        return "\n".join(report_lines)

    async def trigger_bot_restart(self, reason: str):
        self.log.error(f"AUTOMATIC BOT RESTART TRIGGERED: {reason}")
        try:
            if self.cfg.ADMIN_CHAT_ID:
                await self.mq.add_to_queue(self.cfg.ADMIN_CHAT_ID, f"АВТОМАТИЧЕСКИЙ ПЕРЕЗАПУСК БОТА!\n<b>Причина:</b> {reason}\nБот попытается перезапуститься. Пожалуйста, проверьте логи, если проблема повторится.", message_type="send", parse_mode=enums.ParseMode.HTML)
        except Exception as e_notify_admin:
            self.log.error(f"Failed to queue admin notification about automatic restart: {e_notify_admin}")

        await self._shutdown_resources(graceful_queue_shutdown=True, save_data=True)

        self.log.info("Attempting to stop the current event loop for automatic restart...")
        try:
            loop = asyncio.get_running_loop()
            loop.stop()
        except RuntimeError:
            self.log.warning("No running event loop to stop for automatic restart, or already stopping.")
        except Exception as e_loop_stop:
            self.log.error(f"Error stopping event loop for automatic restart: {e_loop_stop}")

        self.log.info(f"Executing automatic restart: {sys.executable} {' '.join(sys.argv)}")
        try:
            os.execl(sys.executable, sys.executable, *sys.argv)
        except Exception as e_execl:
            self.log.critical(f"CRITICAL: os.execl failed during automatic restart: {e_execl}. Bot will exit.");
            sys.exit(1)

    async def handle_message(self, msg: types.Message):
        cid = msg.chat.id
        txt = (msg.text or "").strip()
        usr = self.ds.users.get(cid)

        if txt == "/formative":
            if not usr: await self.send(cid, "Сначала настрой регистрацию через /settings."); return
            elif usr.get("user_mode") != "personal": await self.send(cid, "Команда /formative доступна только для персонального режима."); return
            elif usr.get("user_mode") == "personal":
                student_fio = usr.get("student"); student_class = usr.get("class")
                if student_fio and student_class:
                    formatives_text = await self.get_student_formatives(student_fio, student_class)
                    await self.send_long(cid, formatives_text)
                else: await self.send(cid, "Не удалось определить ФИО или класс из настроек. Пройди настройку через /settings.")
                return

        if txt == "/absent":
            if not usr: await self.send(cid, "Сначала настрой персональную подписку через /settings, чтобы использовать эту команду."); return
            elif usr.get("user_mode") != "personal": await self.send(cid, "Команда /absent доступна только для персонального режима."); return
            elif usr.get("user_mode") == "personal":
                student_fio = usr.get("student"); student_class = usr.get("class")
                if student_fio and student_class:
                    await self.send(cid, "Так как НВТП, физкультура и глоб. компетенции не аттестуются, по ним нет информации о пропусках.")
                    await self.send(cid, "Справка по символам: \nж/н - без уважительной причины\nд/п - по уважительной причине\nа/б - по болезни\nбос/осв - освобождение")
                    absences_text = await self.get_student_absences(student_fio, student_class)
                    await self.send_long(cid, absences_text)
                else: await self.send(cid, "Не удалось определить ваше ФИО или класс из настроек. Пожалуйста, пройди настройку через /settings.")
                return

        if cid not in self.ds.users:
            self.ds.users[cid] = {
                "user_mode": None,
                "registration_role": None,
                "awaiting_role": True,
                "awaiting_class": False,
                "awaiting_student": False,
                "awaiting_partial": False,
                "pending_target": None,
                "class": None,
                "student": None,
                "classes": [],
                "teacher_daily_time": self.cfg.DEFAULT_TEACHER_DIGEST_TIME,
                "teacher_pending_notifications": [],
                "teacher_last_digest_date": None,
                "admin": cid == self.cfg.ADMIN_CHAT_ID,
            }
            await self.ds.save_all_data_to_db()
            role_keys = [
                [{"text": "Я — учитель", "callback_data": "role|teacher"}],
                [{"text": "Я — обучающийся", "callback_data": "role|personal"}],
            ]
            await self.send_kb(cid, "Выберите роль для продолжения:", role_keys)
            return


        usr = self.ds.users[cid]

        role_updated = False
        if "registration_role" not in usr:
            usr["registration_role"] = None
            role_updated = True
        if "awaiting_role" not in usr:
            usr["awaiting_role"] = False
            role_updated = True
        if "classes" not in usr:
            usr["classes"] = []
            role_updated = True
        if not usr.get("teacher_daily_time"):
            usr["teacher_daily_time"] = self.cfg.DEFAULT_TEACHER_DIGEST_TIME
            role_updated = True
        if role_updated:
            await self.ds.save_all_data_to_db()

        if usr.get("user_mode") in {"global", "partial"}:
            usr.update({
                "user_mode": None,
                "registration_role": None,
                "awaiting_role": True,
                "awaiting_class": False,
                "awaiting_student": False,
                "class": None,
                "student": None,
                "teacher_pending_notifications": [],
                "teacher_last_digest_date": None,
            })
            await self.ds.save_all_data_to_db()
            role_keys = [
                [{"text": "Учитель", "callback_data": "role|teacher"}],
                [{"text": "Ученик", "callback_data": "role|personal"}],
            ]
            await self.send_kb(cid, "Формат подписок обновлён. Пожалуйста, выберите роль заново.", role_keys)
            return

        if usr.get("awaiting_role"):
            role_keys = [
                [{"text": "Учитель", "callback_data": "role|teacher"}],
                [{"text": "Ученик", "callback_data": "role|personal"}],
            ]
            await self.send_kb(cid, "Выберите роль для продолжения:", role_keys)
            return

        if usr.get("awaiting_partial"):
            tgt_uid_str, parts_str = usr.get("pending_target"), re.split(r"[,\s]+", txt)
            if tgt_uid_str is None:
                await self.send(cid, "Ошибка: не указан целевой пользователь для настройки частичной подписки.")
                usr.update({"awaiting_partial": False, "pending_target": None}); await self.ds.save_all_data_to_db(); return # UPDATED
            all_configurable_classes = list(self.cfg.CLASS_STUDENTS_URLS.keys())
            selected_classes_for_target = []
            try: selected_classes_for_target = [all_configurable_classes[int(p)-1] for p in parts_str if p.isdigit() and 1 <= int(p) <= len(all_configurable_classes)]
            except IndexError: await self.send(cid, "Ошибка: указан неверный номер класса."); return
            target_uid = int(tgt_uid_str)
            if target_uid in self.ds.users:
                self.ds.users[target_uid].update({"classes": selected_classes_for_target, "user_mode": "partial"})
                await self.send(cid, f"Частичная подписка для пользователя {target_uid} настроена на классы: {', '.join(selected_classes_for_target) or 'нет'}.")
            else: await self.send(cid, f"Ошибка: Пользователь {target_uid} не найден.")
            usr.update({"awaiting_partial": False, "pending_target": None})
            await self.ds.save_all_data_to_db()
            return

        if usr.get("awaiting_class") or usr.get("awaiting_student"):
            await self.send(cid, "Пожалуйста, используй кнопки для завершения настройки."); return

        if txt.startswith("/teacher_time"):
            if usr.get("user_mode") != "teacher":
                await self.send(cid, "Эта команда доступна только для учителей. Переключите режим через /settings.")
                return
            parts = txt.split(maxsplit=1)
            if len(parts) < 2 or not parts[1].strip():
                current = usr.get("teacher_daily_time")
                if current:
                    await self.send(cid, f"Текущее время ежедневной рассылки: {current}. Укажите новое время в формате ЧЧ:ММ, например /teacher_time 21:30")
                else:
                    await self.send(cid, "Укажите желаемое время рассылки в формате ЧЧ:ММ, например /teacher_time 21:30")
                return
            time_candidate = parts[1].strip()
            try:
                hour_str, minute_str = time_candidate.split(":", 1)
                hour, minute = int(hour_str), int(minute_str)
                if not (0 <= hour <= 23 and 0 <= minute <= 59):
                    raise ValueError
                normalized_time = f"{hour:02d}:{minute:02d}"
            except ValueError:
                await self.send(cid, "Некорректный формат времени. Используйте ЧЧ:ММ, например 07:45 или 20:30.")
                return
            usr["teacher_daily_time"] = normalized_time
            usr["teacher_last_digest_date"] = None
            await self.ds.save_all_data_to_db()
            await self.send(cid, f"Ежедневное уведомление будет отправляться в {normalized_time}.")
            return

        if txt == "/status":
            global START_TIME, UPTIME_OFFSET
            uptime_seconds = time.time() - START_TIME + UPTIME_OFFSET
            uptime_formatted = format_hms(uptime_seconds)
            await self.send(cid, f"Состояние мониторинга: {'включен' if self.ds.enabled else 'выключен'}\nАптайм: {uptime_formatted}")
        elif txt == "/help":
            admin_help_text = ""
            if usr.get("admin"):
                admin_help_text = "\n\n<b>Команды администратора:</b>\n/disable - выключить проверки\n/enable - включить проверки\n/list - список пользователей\n/name [uid] - вывести имя аккаунта по ID\n/notify [текст] - сообщение всем\n\n/msg [uid] [текст] - личное сообщение пользователю\n/set [uid] [mode] [args] - изменить настройки юзера (mode: personal, global, partial, none)\n/restart - перезапуск бота\n/stop - graceful остановка бота\n/fast_stop - остановка бота без сохранения MessageQueue\n/log - показать лог\n/force_fetch - инициировать проверку немедленно\n/delete uid - удалить пользователя\n/resources - загруженность программы и ресурсов"
            await self.send(cid, "<b>Доступные команды:</b>\n/status - статус бота и проверок\n/me - информация обо мне\n/absent - получить сводку о пропусках\n/formative - получить сводку о ФО\n/help - это сообщение" + admin_help_text)
        elif txt == "/settings":
            usr.update({
                "user_mode": None,
                "registration_role": None,
                "awaiting_role": True,
                "awaiting_class": False,
                "awaiting_student": False,
                "class": None,
                "student": None,
                "teacher_pending_notifications": [],
                "teacher_last_digest_date": None,
            })
            await self.ds.save_all_data_to_db()
            role_keys = [
                [{"text": "Учитель", "callback_data": "role|teacher"}],
                [{"text": "Ученик", "callback_data": "role|personal"}],
            ]
            await self.send_kb(cid, "Выберите роль для продолжения:", role_keys)
            return

        elif txt == "/me":
            mode = usr.get('user_mode', "не задан"); mode_str = str(mode)
            if mode == "personal": mode_str = "personal"
            elif mode == "global": mode_str = "глобальный (все классы)"
            elif mode == "partial": mode_str = f"частичный (классы: {', '.join(usr.get('classes',[])) or 'не выбраны'})"
            elif mode is None or mode == "none": mode_str = "отключен"
            await self.send(cid,f"<b>Твои текущие настройки:</b>\nID чата: {cid}\nРежим уведомлений: {mode_str}\nВыбранный класс: {usr.get('class') or '-'}\nВыбранный ученик: {usr.get('student') or '-'}")

        if usr.get("admin"):

            if txt == "/disable": self.ds.enabled = False; await self.ds.save_all_data_to_db(); await self.send(cid, "Проверки оценок остановлены.")

            elif txt == "/enable": self.ds.enabled = True; await self.ds.save_all_data_to_db(); await self.send(cid, "Проверки оценок включены.")

            elif txt.startswith("/notify "):
                message_to_broadcast = txt.split(' ',1)
                if len(message_to_broadcast) > 1 and message_to_broadcast[1].strip():
                    await self.send(cid, "Сообщение отправлено в очередь для рассылки."); await self.broadcast(f"{message_to_broadcast[1]}")
                else: await self.send(cid, "Пожалуйста, укажите текст сообщения после /notify.")


            elif txt.startswith("/msg"):
                parts_msg = txt.split(maxsplit=2)
                if len(parts_msg) < 3 or not parts_msg[1].strip() or not parts_msg[2].strip():
                    await self.send(cid, "Usage: /msg <uid> <message>")
                else:
                    target_uid_str = parts_msg[1].strip()
                    message_body = parts_msg[2].strip()
                    try:
                        target_uid = int(target_uid_str)
                    except ValueError:
                        await self.send(cid, "Invalid UID. UID must be a number.")
                    else:
                        try:
                            await self.send(target_uid, message_body)
                        except Exception as e_msg:
                            self.log.exception(e_msg)
                            await self.send(cid, f"Failed to queue message for {target_uid}: {e_msg}")
                        else:
                            warning_suffix = "" if target_uid in self.ds.users else " (user not registered in the bot yet)"
                            await self.send(cid, f"Message queued for {target_uid}{warning_suffix}.")
                            self.log.info(f"Admin {cid} queued direct message to {target_uid}.")

            elif txt.startswith("/name"):
                parts_name = txt.split(maxsplit=1)
                if len(parts_name) < 2 or not parts_name[1].strip():
                    await self.send(cid, "Использование: /name uid")
                else:
                    target_uid_str = parts_name[1].strip()
                    try:
                        target_uid = int(target_uid_str)
                    except ValueError:
                        await self.send(cid, "Неверный формат UID. UID должен быть числом.")
                    else:
                        try:
                            chat_info = await self.bot.get_chat(target_uid)
                            display_name = (
                                getattr(chat_info, "full_name", None)
                                or getattr(chat_info, "title", None)
                                or getattr(chat_info, "first_name", None)
                            )
                            if isinstance(display_name, str):
                                display_name = display_name.strip() or "Имя не указано"
                            else:
                                display_name = "Имя не указано"
                            response_lines = [f"Имя аккаунта {target_uid}: {display_name}"]
                            username = getattr(chat_info, "username", None)
                            if username:
                                response_lines.append(f"Username: @{username}")
                            else:
                                response_lines.append("Username не указан.")
                            await self.send(cid, "\n".join(response_lines))
                        except TelegramForbiddenError:
                            await self.send(cid, f"Нет доступа к информации о пользователе {target_uid}.")
                        except TelegramBadRequest as e_chat:
                            await self.send(cid, f"Не удалось получить данные пользователя {target_uid}: {e_chat}")
                        except Exception as e_name:
                            self.log.exception(e_name)
                            await self.send(cid, f"Ошибка при получении данных пользователя {target_uid}: {e_name}")

            elif txt.startswith("/delete "):
                parts_delete = txt.split(maxsplit=1)
                if len(parts_delete) < 2 or not parts_delete[1].strip(): await self.send(cid, "Использование: /delete uid")
                else:
                    try:
                        uid_to_delete = int(parts_delete[1].strip())
                        if uid_to_delete == cid: await self.send(cid, f"Вы пытаетесь удалить себя (Администратора). Это действие разрешено, но будьте осторожны.")
                        deletion_status = await self.ds.delete_user(uid_to_delete)
                        if deletion_status == "success":
                            await self.send(cid, f"Пользователь с ID {uid_to_delete} успешно удален."); self.log.info(f"Admin {cid} deleted user {uid_to_delete}.")
                        elif deletion_status == "not_found":
                            await self.send(cid, f"Пользователь с ID {uid_to_delete} не найден.")
                        else:
                            await self.send(cid, f"Не удалось удалить пользователя {uid_to_delete}. Попробуйте позже или проверьте логи.")
                    except ValueError: await self.send(cid, "Неверный формат UID. UID должен быть числом.")
                    except Exception as e_del_user: self.log.error(f"Error deleting user: {e_del_user}"); self.log.exception(e_del_user); await self.send(cid, f"Произошла ошибка при удалении пользователя: {e_del_user}")

            elif txt == "/log": log_content = self.log.get_logs(); await self.send_long(cid, log_content if log_content else "Лог пуст.")

            elif txt == "/list":
                msg_parts = ["<b>Список пользователей и их настроек:</b>\n"]
                if not self.ds.users: msg_parts.append("Пользователи еще не зарегистрированы.")
                else:
                    for u_id, u_set in self.ds.users.items():
                        m = u_set.get("user_mode"); ms = str(m); cl = u_set.get('classes',[])
                        if m is None or m == "none": ms = "отключен"
                        elif m=="personal": ms = "личный"
                        elif m=="teacher": ms = f"учитель ({u_set.get('class') or 'не задан'})"
                        elif m=="global": ms = "глобальный"
                        elif m=="partial": ms = f"частичный ({','.join(cl) or 'нет'})"
                        admin_status = " (Admin)" if u_set.get("admin") else ""
                        msg_parts.append(f"\n<b>ID:</b> {u_id}{admin_status}\n  Режим: {ms}\n  Класс: {u_set.get('class') or '-'}\n  Ученик: {u_set.get('student') or '-'}")
                await self.send_long(cid, "".join(msg_parts))

            elif txt.startswith("/set "):
                parts = txt.split(maxsplit=3)
                if len(parts) < 3: await self.send(cid, "Подсказка: /set <uid> <mode> [аргументы]"
                            "\nРежимы: personal, teacher, none."); return
                try:
                    target_uid_to_set = int(parts[1]); mode_to_set = parts[2].lower()
                    if target_uid_to_set not in self.ds.users:
                        self.ds.users[target_uid_to_set] = {
                            "user_mode": None,
                            "registration_role": None,
                            "awaiting_role": False,
                            "awaiting_class": False,
                            "awaiting_student": False,
                            "awaiting_partial": False,
                            "pending_target": None,
                            "class": None,
                            "student": None,
                            "classes": [],
                            "teacher_daily_time": self.cfg.DEFAULT_TEACHER_DIGEST_TIME,
                            "teacher_pending_notifications": [],
                            "teacher_last_digest_date": None,
                            "admin": target_uid_to_set == self.cfg.ADMIN_CHAT_ID,
                        }
                    target_record = self.ds.users[target_uid_to_set]
                    if mode_to_set == "personal":
                        if len(parts) < 4:
                            await self.send(cid, "Для режима 'personal' укажите ученика: /set <uid> personal Фамилия_Имя."); return
                        student_name_to_set = parts[3].replace("_", " ")
                        target_record.update({
                            "user_mode": "personal",
                            "registration_role": "personal",
                            "student": student_name_to_set,
                            "awaiting_role": False,
                            "awaiting_class": False,
                            "awaiting_student": False,
                        })
                        await self.send(cid, f"Пользователю {target_uid_to_set} установлен режим 'personal' для ученика '{student_name_to_set}'. При необходимости он может перепройти настройку через /settings.")
                    elif mode_to_set == "teacher":
                        if len(parts) < 4:
                            await self.send(cid, "Для режима 'teacher' укажите класс: /set <uid> teacher Класс."); return
                        teacher_class = parts[3].replace("_", " ")
                        target_record.update({
                            "user_mode": "teacher",
                            "registration_role": "teacher",
                            "class": teacher_class,
                            "student": None,
                            "awaiting_role": False,
                            "awaiting_class": False,
                            "awaiting_student": False,
                        })
                        if not target_record.get("teacher_daily_time"):
                            target_record["teacher_daily_time"] = self.cfg.DEFAULT_TEACHER_DIGEST_TIME
                        if not target_record.get("teacher_last_digest_date"):
                            try:
                                def_hour, def_min = map(int, self.cfg.DEFAULT_TEACHER_DIGEST_TIME.split(":", 1))
                                default_minutes = def_hour * 60 + def_min
                                now_dt = datetime.now()
                                if now_dt.hour * 60 + now_dt.minute >= default_minutes:
                                    target_record["teacher_last_digest_date"] = now_dt.strftime("%Y-%m-%d")
                            except ValueError:
                                pass
                        await self.send(cid, f"Пользователю {target_uid_to_set} установлен режим 'teacher' для класса '{teacher_class}'.")
                    elif mode_to_set == "none":
                        target_record.update({
                            "user_mode": None,
                            "registration_role": None,
                            "class": None,
                            "student": None,
                            "awaiting_role": False,
                            "awaiting_class": False,
                            "awaiting_student": False,
                        })
                        await self.send(cid, f"У пользователя {target_uid_to_set} отключены уведомления.")
                    else:
                        await self.send(cid, "Неизвестный режим. Доступные варианты: personal, teacher, none.")
                        return
                    await self.ds.save_all_data_to_db()
                except ValueError: await self.send(cid, "Некорректный идентификатор пользователя. UID должен быть числом.")
                except Exception as e_set: self.log.exception(e_set); await self.send(cid, f"Произошла ошибка при обновлении настроек: {e_set}")

            elif txt == "/force_fetch":
                global GRADES_MONITOR_INSTANCE 
                if GRADES_MONITOR_INSTANCE:
                    await self.send(cid, "Инициирую принудительное обновление данных по оценкам...")
                    await GRADES_MONITOR_INSTANCE.trigger_immediate_check()
                    await self.send(cid, "Команда на обновление отправлена.")
                else: await self.send(cid, "Экземпляр монитора оценок не найден. Обновление невозможно.")
            
            elif txt == "/restart":
                await self.execute_restart("Admin command")
            
            elif txt == "/stop":
                await self.execute_stop(cid)
            
            elif txt == "/fast_stop":
                await self.execute_fast_stop(cid)
            
            elif txt == "/resources":
                await self.send_resources_analysis(cid)

    async def handle_callback(self, cb: types.CallbackQuery):
        cid = cb.message.chat.id
        data = cb.data
        try: await cb.answer()
        except Exception as e_ans: self.log.warning(f"Could not answer callback query for {cid}: {e_ans}")

        if cid not in self.ds.users:
            self.log.warning(f"Callback от неизвестного пользователя {cid} (data: {data}). Игнорируется.")
            try: await cb.message.delete()
            except Exception: pass; return

        usr = self.ds.users[cid]

        if data.startswith("role|") and usr.get("awaiting_role"):
            chosen_role = data.split("|", 1)[1]
            class_names_for_kb = list(self.cfg.CLASS_STUDENTS_URLS.keys())
            usr.update({
                "registration_role": None,
                "awaiting_role": False,
                "awaiting_class": False,
                "awaiting_student": False,
                "student": None,
                "class": None,
            })
            await self.ds.save_all_data_to_db()

            if chosen_role == "teacher":
                if not class_names_for_kb:
                    await self.send(cid, "Нет доступных классов для выбора.")
                else:
                    taken_classes = {
                        info.get("class")
                        for uid, info in self.ds.users.items()
                        if uid != cid and info.get("user_mode") == "teacher" and info.get("class")
                    }
                    available_classes = [c for c in class_names_for_kb if c not in taken_classes]
                    if not available_classes:
                        await self.send(cid, "Все классы уже закреплены за другими учителями. Обратитесь к администратору, если это ошибка.")
                        usr.update({"awaiting_role": True})
                        await self.ds.save_all_data_to_db()
                        try: await cb.message.delete()
                        except Exception: pass
                        return
                    usr.update({"registration_role": "teacher", "awaiting_class": True})
                    await self.ds.save_all_data_to_db()
                    keys = [[{"text": c, "callback_data": f"cls|{c}"}] for c in available_classes]
                    await self.send_kb(cid, "Теперь выберите свой класс:", keys)

            elif chosen_role == "personal":
                if not class_names_for_kb:
                    await self.send(cid, "Нет доступных классов для выбора.")
                else:
                    usr.update({"registration_role": "personal", "awaiting_class": True})
                    await self.ds.save_all_data_to_db()
                    keys = [[{"text": c, "callback_data": f"cls|{c}"}] for c in class_names_for_kb]
                    await self.send_kb(cid, "Теперь выбери свой класс:", keys)

            else:
                usr.update({"awaiting_role": True})
                await self.ds.save_all_data_to_db()
                await self.send(cid, "Неизвестная роль. Пожалуйста, попробуйте снова.")
            try: await cb.message.delete()
            except Exception: pass
            return

        if data.startswith("cls|") and usr.get("awaiting_class"):
            cls_name = data.split("|",1)[1]
            usr.update({"class": cls_name, "student": None})
            registration_role = usr.get("registration_role")
            if registration_role == "teacher":
                usr.update({"awaiting_class": False, "awaiting_student": False, "user_mode": "teacher"})
                if not usr.get("teacher_daily_time"):
                    usr["teacher_daily_time"] = self.cfg.DEFAULT_TEACHER_DIGEST_TIME
                if not usr.get("teacher_last_digest_date"):
                    try:
                        default_hour, default_minute = map(int, self.cfg.DEFAULT_TEACHER_DIGEST_TIME.split(":", 1))
                        default_minutes = default_hour * 60 + default_minute
                        now_dt = datetime.now()
                        if now_dt.hour * 60 + now_dt.minute >= default_minutes:
                            usr["teacher_last_digest_date"] = now_dt.strftime("%Y-%m-%d")
                    except ValueError:
                        pass
                await self.ds.save_all_data_to_db()
                self.log.info(f"Teacher subscription configured/updated: User {cid} for class {cls_name}")
                if cid != self.cfg.ADMIN_CHAT_ID:
                    try:
                        admin_chat_id_val = int(self.cfg.ADMIN_CHAT_ID)
                        digest_time = usr.get("teacher_daily_time") or self.cfg.DEFAULT_TEACHER_DIGEST_TIME
                        await self.send(
                            admin_chat_id_val,
                            f"Новая/обновлённая учительская подписка:\nID пользователя: {cid}\nКласс: {cls_name}\nЕжедневное уведомление: {digest_time}"
                        )
                    except ValueError:
                        self.log.error(f"ADMIN_CHAT_ID in config is not a valid integer: {self.cfg.ADMIN_CHAT_ID}")
                    except Exception as e_admin_notify:
                        self.log.error(f"Failed to notify admin about new teacher subscription: {e_admin_notify}")
                await self.send(cid, f"Хорошо, для вас настроен учительский режим уведомлений. \n\nПо умолчанию, вы будете получать сводку изменений по вашему классу 1 раз в день в 8:00. \nЧтобы изменить время сводки используйте команду /teacher_time")
                try: await cb.message.delete()
                except Exception: pass
                return
            usr.update({"awaiting_class": False, "awaiting_student": True})
            await self.ds.save_all_data_to_db()

            students_in_class = self.ds.students.get(cls_name, [])
            if not students_in_class:
                await self.send(cid, f"В классе {cls_name} не найдено учеников. Если это ошибка, обратитесь к администратору.")
                usr.update({"awaiting_class": True, "awaiting_student": False, "class": None}); await self.ds.save_all_data_to_db(); 
                try: await cb.message.delete()
                except Exception: pass; return

            associated_students_by_others = set()
            for user_id_db, user_data_db in self.ds.users.items():
                if user_id_db != cid and user_data_db.get("student") and user_data_db.get("class") == cls_name:
                    associated_students_by_others.add(user_data_db.get("student"))
            available_students = [s for s in students_in_class if s not in associated_students_by_others]
            choices = sorted(list(set(available_students)))

            if not choices:
                await self.send(cid, f"В классе {cls_name} нет свободных студентов (вероятно, они уже заняты в личных подписках или список учеников пуст).")
                usr.update({"awaiting_class": True, "awaiting_student": False, "class": None}); await self.ds.save_all_data_to_db(); 
                try: await cb.message.delete()
                except Exception: pass; return

            keys = [[{"text": s, "callback_data": f"stu|{s}"}] for s in choices]
            await self.send_kb(cid, f"Класс {cls_name}. Выбери себя из списка:", keys)
            try: await cb.message.delete()
            except Exception: pass
            return


        elif data.startswith("stu|") and usr.get("awaiting_student"):
            student_name = data.split("|",1)[1]
            selected_class = usr.get("class")
            is_already_taken_by_another = False
            for user_id_db, user_data_db in self.ds.users.items():
                if user_id_db != cid and user_data_db.get("student") == student_name and user_data_db.get("class") == selected_class:
                    is_already_taken_by_another = True; break
            if is_already_taken_by_another:
                await self.send(cid, f"Ученик {student_name} из класса {selected_class} только что был выбран другим пользователем. Пожалуйста, выбери другого ученика или начни настройку заново через /settings.")
            else:
                usr.update({"student": student_name, "awaiting_student":False, "user_mode": "personal"})
                await self.ds.save_all_data_to_db()
                await self.send(cid, f"Отлично! Настройки сохранены: тебя зовут {student_name}, ты из {selected_class} класса. Ожидай персональные уведомления об изменениях оценок. Доступные команды — /help")
                self.log.info(f"Personal subscription configured/updated: User {cid} for student {student_name} in class {selected_class}")
                if cid != self.cfg.ADMIN_CHAT_ID:
                    try:
                        admin_chat_id_val = int(self.cfg.ADMIN_CHAT_ID)
                        await self.send(admin_chat_id_val, f"Новая/обновленная персональная подписка:\nID пользователя: {cid}\nФИО ученика: {student_name}\nКласс: {selected_class}")
                    except Exception as e_admin_notify: self.log.error(f"Failed to notify admin about new subscription: {e_admin_notify}")
            try: await cb.message.delete()
            except Exception: pass

# ───────────────────────────────────────────────────────────────────────────────
# 7. GRADES MONITOR
# ───────────────────────────────────────────────────────────────────────────────
GRADES_MONITOR_INSTANCE: Optional['GradesMonitor'] = None

class GradesMonitor:
    def __init__(self, cfg: Config, ds: SQLDB, http_fetcher: AsyncHTTPDataFetcher, tbot: 'TelegramBot', log: Logger):
        self.cfg = cfg
        self.ds = ds
        self.fetcher = http_fetcher
        self.tb = tbot
        self.log = log
        
        self.min_interval, self.max_interval = 60, cfg.CHECK_INTERVAL
        self.subject_tasks_meta: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
        
        global GRADES_MONITOR_INSTANCE
        GRADES_MONITOR_INSTANCE = self

        self.consecutive_teacher_id_failures = 0
        self.max_teacher_id_failures = cfg.MAX_CONSECUTIVE_TEACHER_ID_FAILURES
        self.teacher_id_failure_restart_cooldown = cfg.TEACHER_ID_FAILURE_RESTART_COOLDOWN
        self.last_teacher_id_failure_restart_ts = 0.0
        self.stop_processing_due_to_critical_errors = False
        self._failure_counter_lock = asyncio.Lock()

    async def handle_teacher_id_fetch_failure(self) -> bool:
        async with self._failure_counter_lock:
            if self.stop_processing_due_to_critical_errors:
                return True 

            current_time = time.time()
            if current_time < self.last_teacher_id_failure_restart_ts + self.teacher_id_failure_restart_cooldown:
                self.log.warning(f"Teacher ID fetch failure detected within cooldown period. Not incrementing primary counter yet. Last restart at: {datetime.fromtimestamp(self.last_teacher_id_failure_restart_ts)}")
                return False 

            self.consecutive_teacher_id_failures += 1
            self.log.warning(f"Consecutive critical teacher_id fetch failures: {self.consecutive_teacher_id_failures}/{self.max_teacher_id_failures}")

            if self.consecutive_teacher_id_failures >= self.max_teacher_id_failures:
                self.log.error(f"Max consecutive teacher_id fetch failures ({self.max_teacher_id_failures}) reached. Initiating bot restart.")
                self.stop_processing_due_to_critical_errors = True
                self.last_teacher_id_failure_restart_ts = current_time
                self.consecutive_teacher_id_failures = 0 
                await self.tb.trigger_bot_restart("Критическая ошибка: множественные сбои получения данных учителя (Teacher ID).")
                return True
        return False

    async def reset_teacher_id_failure_count(self):
        async with self._failure_counter_lock:
            if self.consecutive_teacher_id_failures > 0:
                self.log.info(f"Successful teacher_id related fetch. Resetting failure counter from {self.consecutive_teacher_id_failures}.")
                self.consecutive_teacher_id_failures = 0

    async def trigger_immediate_check(self):
        self.log.info("Force fetch: Setting intervals to 1s for next check.")
        for subject_group in self.subject_tasks_meta.values():
            for task_info in subject_group:
                if task_info.get('task_obj'):
                    task_instance = task_info['task_obj']
                    if hasattr(task_instance, 'current_interval'):
                         task_instance.current_interval = 1


    class SubjectTask:
        __slots__ = ("subject_name", "class_name", "url", "monitor_ref", "current_interval", "is_first_run", "class_id", "predmet_id", "last_success_time", "last_full_fetch_ts")
        def __init__(self, subject_name: str, class_name: str, url: str, monitor_ref: 'GradesMonitor'):
            self.subject_name, self.class_name, self.url = subject_name, class_name, url
            self.monitor_ref = monitor_ref
            self.last_success_time: Optional[float] = None
            self.current_interval, self.is_first_run = monitor_ref.cfg.CHECK_INTERVAL, True 
            self.class_id, self.predmet_id = parse_url_to_get_ids(url)
            self.last_full_fetch_ts: float = time.time()

        async def run_loop(self):
            ds, tb, log, cfg, fetcher = self.monitor_ref.ds, self.monitor_ref.tb, self.monitor_ref.log, self.monitor_ref.cfg, self.monitor_ref.fetcher
            log_ctx = f"{self.subject_name}({self.class_name})"
            if not self.class_id or not self.predmet_id: log.error(f"[{log_ctx}] Invalid URL: {self.url}. Task stopped."); return

            while True:
                if not self.is_first_run: await asyncio.sleep(self.current_interval)
                else: await asyncio.sleep(1) 
                
                if self.monitor_ref.stop_processing_due_to_critical_errors:
                    log.info(f"[{log_ctx}] GradesMonitor processing is stopped due to critical errors. Task pausing.")
                    await asyncio.sleep(30)
                    continue
                
                if not ds.enabled:
                    await asyncio.sleep(10); continue
                
                now = time.time()
                need_full_fetch = now - self.last_full_fetch_ts >= cfg.NON_CURRENT_FETCH_INTERVAL

                if self.is_first_run:
                    quarters = [cfg.CURRENT_MONITORING_QUARTER]  # только текущая
                elif need_full_fetch:
                    quarters = range(1, 5)                     # все четверти
                    self.last_full_fetch_ts = now
                else:
                    quarters = [cfg.CURRENT_MONITORING_QUARTER]  # только текущая
                
                try:
                    old_native_data = ds.grades.get(self.url)

                    new_native_data, get_predmet_info_failed = await fetcher.fetch_subject_data(self.class_id, self.predmet_id, quarters_to_fetch=quarters)
                    
                    should_restart_now = False
                    if get_predmet_info_failed:
                        log.warning(f"[{log_ctx}] fetch_subject_data indicated 'get-predmet-info' failed. Handling potential critical failure.")
                        should_restart_now = await self.monitor_ref.handle_teacher_id_fetch_failure()
                    else:
                        await self.monitor_ref.reset_teacher_id_failure_count()

                    if should_restart_now:
                        log.error(f"[{log_ctx}] Bot restart triggered by critical teacher_id fetch failures. Terminating task.")
                        return 

                    if not new_native_data:
                        log.warning(f"[{log_ctx}] No data returned by fetch_subject_data. Skipping comparison. GetPredmetInfoFailFlag: {get_predmet_info_failed}")
                        self.current_interval = min(self.current_interval * 1.5, cfg.CHECK_INTERVAL)
                        if self.is_first_run: self.is_first_run = False
                        continue

                    self.last_success_time = time.time()
                    structured_diff = compare_native_data(old_native_data, new_native_data)
                    
                    if structured_diff:
                        log.info(f"[{log_ctx}] Changes detected (native comparison).")
                        subject_info = {"subject_display_name": self.subject_name, "class_name": self.class_name, "url": self.url}
                        await tb.notify_structured_changes(subject_info, structured_diff)
                        
                        ds.grades[self.url] = new_native_data 
                        await ds.save_all_data_to_db()
                        
                        self.current_interval = self.monitor_ref.min_interval
                        base_subj = self.subject_name.split(" ")[0]
                        for sister_task_info in self.monitor_ref.subject_tasks_meta.get(base_subj, []):
                            sister_task_obj = sister_task_info.get('task_obj')
                            if sister_task_obj != self and hasattr(sister_task_obj, 'current_interval'):
                                sister_task_obj.current_interval = self.monitor_ref.min_interval
                    else:
                        log.info(f"[{log_ctx}] Changes NOT detected (native comparison).")
                    
                    if self.is_first_run: self.is_first_run = False
                    if not structured_diff:
                        self.current_interval = min(self.current_interval * 1.5, cfg.CHECK_INTERVAL)
                    
                except Exception as e:
                    log.error(f"[{log_ctx}] Loop error: {e}"); log.exception(e)
                    if isinstance(e, (requests.exceptions.ConnectionError, requests.exceptions.Timeout)):
                        log.info(f"[{log_ctx}] Network error, HTTP fetcher will attempt relogin on next call.")
                    await asyncio.sleep(60)

    async def initial_student_and_grade_population(self):
        self.log.info("Starting initial student list population and grade snapshot check...")
        if not self.fetcher: 
            self.log.error("HTTP Fetcher not available during initial population.")
            return 
        if not self.fetcher._is_logged_in: 
            self.log.info("HTTP Fetcher not logged in, attempting login for initial population...")
            if not await self.fetcher.login():
                self.log.error("HTTP Fetcher login failed. Cannot populate initial data. Student lists might be empty or from DB snapshot.")

        self.log.info("Populating student lists from designated CLASS_STUDENTS_URLS...")
        all_students_by_class = defaultdict(set)
        fetched_data_cache: Dict[str, Optional[Dict]] = {}

        if self.cfg.CLASS_STUDENTS_URLS:
            for class_name, student_list_url in self.cfg.CLASS_STUDENTS_URLS.items():
                self.log.info(f"Fetching student list for class: {class_name} using URL: {student_list_url}")
                class_id, predmet_id = parse_url_to_get_ids(student_list_url)

                if not class_id or not predmet_id:
                    self.log.warning(f"Skipping student list for {class_name} - invalid IDs from URL: {student_list_url} (ClassID: {class_id}, PredmetID: {predmet_id})")
                    continue

                sgs_entry_data, get_predmet_info_failed_flag = await self.fetcher.fetch_subject_data(class_id, predmet_id)
                fetched_data_cache[student_list_url] = sgs_entry_data

                if get_predmet_info_failed_flag:
                    self.log.warning(f"  'get-predmet-info' failed during student list fetch for {class_name} ({class_id}/{predmet_id}). Student list might be incomplete or missing.")

                if sgs_entry_data and 'students_grades' in sgs_entry_data:
                    student_count = 0
                    for student_info in sgs_entry_data['students_grades'].values():
                        fio = student_info.get('fio')
                        if fio:
                            all_students_by_class[class_name].add(fio)
                            student_count += 1
                    self.log.info(f"  Found {student_count} students for class {class_name}.")
                else:
                    self.log.warning(f"  No student data found in sgs_entry_data for {class_name} ({class_id}/{predmet_id}) during student list population. GetPredmetInfoFailFlag: {get_predmet_info_failed_flag}")
        else:
            self.log.warning("CLASS_STUDENTS_URLS is empty in config. Cannot populate student lists automatically.")


        current_students_from_ds = self.ds.students
        updated_student_lists = {cls: sorted(list(names)) for cls, names in all_students_by_class.items()}
        
        if updated_student_lists:
             self.ds.students = updated_student_lists
             self.log.info(f"Successfully populated/updated student lists for {len(self.ds.students)} classes using CLASS_STUDENTS_URLS.")
             await self.ds.save_all_data_to_db()
        elif not current_students_from_ds :
            self.log.warning("Failed to populate any student lists from CLASS_STUDENTS_URLS, and DB snapshot was empty.")
        else:
            self.log.info("Used student lists from existing DB snapshot or no updates from CLASS_STUDENTS_URLS fetch.")

        self.log.info("Checking and establishing NATIVE grade baselines (for all subjects in CLASS_SUBJECT_SITES)...")
        needs_grade_save_for_baselines = False 

        for cls_name_iter, subjects_dict_iter in self.cfg.CLASS_SUBJECT_SITES.items():
            for subject_display_name_iter, url_iter in subjects_dict_iter.items():
                if url_iter not in self.ds.grades or not self.ds.grades.get(url_iter): 
                    log_ctx_iter = f"{subject_display_name_iter}({cls_name_iter})"
                    self.log.info(f"No native baseline in DB snapshot for {log_ctx_iter}. Establishing...")
                    
                    class_id_s, predmet_id_s = parse_url_to_get_ids(url_iter)
                    if class_id_s and predmet_id_s:
                        sgs_subject_entry_data_baseline = None
                        get_predmet_info_failed_flag_baseline = False

                        if url_iter in fetched_data_cache:
                            sgs_subject_entry_data_baseline = fetched_data_cache[url_iter]
                            self.log.info(f"  Reusing cached data for baseline of {log_ctx_iter}.")
                        
                        if sgs_subject_entry_data_baseline is None:
                            self.log.info(f"  Fetching fresh data for baseline of {log_ctx_iter} (not in cache or cache was None)...")
                            sgs_subject_entry_data_baseline, get_predmet_info_failed_flag_baseline = await self.fetcher.fetch_subject_data(class_id_s, predmet_id_s)
                            if get_predmet_info_failed_flag_baseline:
                                self.log.warning(f"    'get-predmet-info' failed during fresh baseline fetch for {log_ctx_iter}.")

                        if sgs_subject_entry_data_baseline: 
                            self.ds.grades[url_iter] = sgs_subject_entry_data_baseline
                            self.log.info(f"  Baselined {log_ctx_iter} with native data.")
                        else: 
                            self.log.warning(f"  Initial baseline fetch FAILED for {log_ctx_iter} (GetPredmetInfoFailFlag: {get_predmet_info_failed_flag_baseline}). Baseline set to empty dict.")
                            self.ds.grades[url_iter] = {}
                        needs_grade_save_for_baselines = True
                    else:
                        self.log.warning(f"Cannot parse IDs for native baseline fetch of {log_ctx_iter} from URL {url_iter}")
        
        if needs_grade_save_for_baselines:
            self.log.info("Saving updated grade baselines to DB...")
            await self.ds.save_all_data_to_db()
        
        self.log.info("Initial student list update and NATIVE grade baseline check complete.")

    async def run(self):
        current_time = time.time()
        if self.stop_processing_due_to_critical_errors and \
           current_time < self.last_teacher_id_failure_restart_ts + self.teacher_id_failure_restart_cooldown:
            self.log.warning("GradesMonitor.run() called, but processing is stopped due to recent critical errors and in cooldown. Not starting tasks.")
            return 
        elif self.stop_processing_due_to_critical_errors:
            self.log.info("Cooldown period after critical error restart has passed. Resetting error state for GradesMonitor.")
            self.stop_processing_due_to_critical_errors = False
            self.consecutive_teacher_id_failures = 0 
    
        await self.initial_student_and_grade_population()
        active_tasks = []
        for cls_name, subjects_dict in self.cfg.CLASS_SUBJECT_SITES.items():
            for subject_display_name, url in subjects_dict.items():
                task_controller = GradesMonitor.SubjectTask(subject_display_name, cls_name, url, self)
                base_subject_name = subject_display_name.split(" ")[0] 
                self.subject_tasks_meta[base_subject_name].append({'task_obj': task_controller, 'url': url})
                active_tasks.append(asyncio.create_task(task_controller.run_loop()))
                LOGGER.info(f"Scheduled continuous monitoring for: {subject_display_name} ({cls_name})")

        if not active_tasks: LOGGER.warning("No monitoring tasks scheduled."); return
        LOGGER.info(f"GradesMonitor continuous monitoring started with {len(active_tasks)} tasks.")
        await asyncio.gather(*active_tasks)

# ───────────────────────────────────────────────────────────────────────────────
# 8. MAIN ENTRYPOINT
# ───────────────────────────────────────────────────────────────────────────────
START_TIME = time.time(); UPTIME_OFFSET = 0

async def main():
    global HTTP_FETCHER, MESSAGE_SENDER_QUEUE, DS, GRADES_MONITOR_INSTANCE 

    config = Config()
    try:
        DS = SQLDB(config.DATABASE_NAME, config) 
    except Exception as e: 
        LOGGER.critical(f"CRITICAL: Failed to initialize SQLDB: {e}. Bot cannot start.")
        sys.exit(1)
    DS.load_config_into_object(config)
    LOGGER.admin_chat_id = config.ADMIN_CHAT_ID 
    HTTP_FETCHER = AsyncHTTPDataFetcher(config, LOGGER)
    if not await HTTP_FETCHER.login():
        LOGGER.error("CRITICAL: Initial login failed. Bot continues but grade fetching will not work until next successful login attempt by the fetcher.")
    else:
        LOGGER.info("Initial HTTP login successful via AsyncHTTPDataFetcher.")
    bot = Bot(token=config.TELEGRAM_TOKEN) 
    dp = Dispatcher()
    LOGGER.bot = bot 
    MESSAGE_SENDER_QUEUE = MessageQueue(bot, LOGGER, rate_limit_per_second=25) 
    MESSAGE_SENDER_QUEUE.start()
    telegram_bot_handler = TelegramBot(config, DS, LOGGER, bot, MESSAGE_SENDER_QUEUE)
    dp.message.register(telegram_bot_handler.handle_message)
    dp.callback_query.register(telegram_bot_handler.handle_callback)
    monitor = GradesMonitor(config, DS, HTTP_FETCHER, telegram_bot_handler, LOGGER) 
    asyncio.create_task(monitor.run())
    
    try:
        await dp.start_polling(bot)
    except asyncio.CancelledError:
        LOGGER.info("Main polling task was cancelled (likely during shutdown).")
    finally:
        LOGGER.info("Main polling loop ended. Finalizing shutdown of services from main()...")
        if MESSAGE_SENDER_QUEUE and MESSAGE_SENDER_QUEUE._task and not MESSAGE_SENDER_QUEUE._task.done(): 
            LOGGER.info("Main finally: Stopping message sender queue...")
            await MESSAGE_SENDER_QUEUE.stop(process_queue=True) 
        
        if HTTP_FETCHER and HTTP_FETCHER.session: 
            LOGGER.info("Main finally: Closing HTTP fetcher session...")
            await HTTP_FETCHER.close_session()
        
        if DS and DS.conn : 
            LOGGER.info("Main finally: Saving data and closing SQLDB connection...")
            await DS.save_all_data_to_db() 
            DS.close_db() 
        
        LOGGER.info("Bot stopped and resources released from main().")

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        LOGGER.info("KeyboardInterrupt received. Shutting down...")
