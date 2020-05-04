@echo off

call grasspile grass.ml -P0 -o grass.grass

if ERRORLEVEL 1 (
  echo compile failed [exitcode=%ERRORLEVEL%]
  exit /b 1
)

echo wWWwwwwvWwWWwWWWw | grass grass.grass
