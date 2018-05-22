-- Copyright 2018 Google LLC
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     https://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE UndecidableInstances      #-}

module Main where

import Control.Applicative
import Control.Monad
import Data.List ((\\), foldl')
import qualified Data.Map as M
import Data.Void
import qualified Data.Set as S
import Debug.Trace
import Diagrams.Backend.Rasterific hiding (size)
import Diagrams.Prelude hiding (zero, shift, size, apply, _tail, _head, sc, Name)
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Lexer as L
import Text.Megaparsec.String
import Text.Printf
import Unbound.LocallyNameless hiding (zero, translate, subst, apply)
import qualified Unbound.LocallyNameless as U

{- Raw representation -}

data Term
  = Var Int
  | Lam Term
  | App Term Term
  deriving (Ord, Eq, Show)

isLam (Lam _) = True
isLam _       = False

pretty :: Term -> String
pretty = pretty' 0 0
 where
  pretty' n l (Var i) = show (n - i - 1)
  pretty' n l (Lam t) =
    parens (l > 0) $ "\\" ++ show n ++ "." ++ (pretty' (n + 1) 0 t)
  pretty' n l (App t1 t2) =
    parens (l > 1) $ pretty' n 1 t1 ++ " " ++ pretty' n 2 t2

  parens b s = if b then "(" ++ s ++ ")" else s


{- Unbound representation -}

data UTerm
  = UVar (Name UTerm)
  | UApp UTerm UTerm
  | ULam (Bind (Name UTerm) UTerm)
  deriving (Show)

derive [''UTerm]

instance Alpha UTerm

instance Subst UTerm UTerm where
  isvar (UVar v) = Just (SubstName v)
  isvar _ = Nothing

ulam x t = ULam $ bind (string2Name x) t
uvar = UVar . string2Name

uterm2term :: UTerm -> Term
uterm2term t = runFreshM $ go 0 M.empty t
 where
  go :: Int -> M.Map (Name UTerm) Int -> UTerm -> FreshM Term
  go d env (UVar x) = return $ Var (d - (get x env) - 1)
  go d env (ULam b) = do
    (x, t) <- unbind b
    Lam <$> go (d + 1) (M.insert x d env) t
  go d env (UApp t u) = App <$> go d env t <*> go d env u

  get x env = case M.lookup x env of
    Nothing -> error (show x ++ " not found")
    Just t  -> t

term2uterm :: Term -> UTerm
term2uterm t = runFreshM $ go [] t
 where
  go env (Var i) = return $ UVar (env !! i)
  go env (Lam t) = do
    x  <- fresh (string2Name "x")
    t' <- go (x : env) t
    return $ ULam (bind x t')
  go env (App t u) = UApp <$> go env t <*> go env u

{- Naive CPS -}

{-
cps :: Term -> Term
cps (Var i) = Var i
cps (Lam t) = Lam (v0 @: Lam (cps (shift 1 1 t)))
cps (App t u) = Lam (cps (shift 0 1 t) @: Lam (v0 @: cps (shift 0 2 u) @: v1))
-}

{- One pass CPS -}

cps :: Term -> Term
cps = uterm2term . runOcps . term2uterm

runOcps :: UTerm -> UTerm
runOcps t = runFreshM $ do
  ocps_t <- ocps t
  return (ocps_t id)

ocps :: Fresh m => UTerm -> m ((UTerm -> UTerm) -> UTerm)
ocps x@(UVar _) = do
  a <- fresh (string2Name "a")
  return $ \ka -> UApp x (ULam (bind a (ka (UVar a))))
ocps (ULam b) = do
  (x, m) <- unbind b
  k      <- fresh (string2Name "k")
  ocps_m <- ocps' m
  return $ \ka -> ka (ULam (bind k (ULam (bind x (ocps_m (UVar k))))))
ocps (UApp t u) = do
  a      <- fresh (string2Name "a")
  ocps_t <- ocps t
  ocps_u <- ocps'' u
  return
    $ \ka -> ocps_t (\m -> UApp (UApp m (ULam (bind a (ka (UVar a))))) ocps_u)

ocps' :: Fresh m => UTerm -> m (UTerm -> UTerm)
ocps' x@(UVar _) = return $ \ka -> UApp x ka
ocps' (  ULam b) = do
  (x, m) <- unbind b
  k      <- fresh (string2Name "k")
  ocps_m <- ocps' m
  return $ \ka -> UApp ka (ULam (bind k (ULam (bind x (ocps_m (UVar k))))))
ocps' (UApp t u) = do
  ocps_t <- ocps t
  ocps_u <- ocps'' u
  return $ \ka -> ocps_t (\m -> UApp (UApp m ka) ocps_u)

ocps'' :: Fresh m => UTerm -> m UTerm
ocps'' x@(UVar _) = return x
ocps'' (  ULam b) = do
  (x, m) <- unbind b
  k1     <- fresh (string2Name "k")
  k2     <- fresh (string2Name "k")
  ocps_m <- ocps' m
  return $ ULam
    (bind k1
          (UApp (UVar k1) (ULam (bind k2 (ULam (bind x (ocps_m (UVar k2)))))))
    )
ocps'' (UApp t u) = do
  ocps_t <- ocps t
  ocps_u <- ocps'' u
  k      <- fresh (string2Name "k")
  return $ ULam (bind k (ocps_t (\m -> UApp (UApp m (UVar k)) ocps_u)))

{- Parser -}

sc = L.space (skipSome spaceChar *> pure ()) lineCmnt blockCmnt
 where
  lineCmnt  = L.skipLineComment "--"
  blockCmnt = L.skipBlockComment "{-" "-}"
lexeme = L.lexeme sc
symbol = L.symbol sc
identifier = (lexeme . try) (p >>= check)
 where
  p = (:) <$> (letterChar <|> char '_') <*> many
    (alphaNumChar <|> char '_' <|> char '\'')
  check x = if x `elem` ["in", "let"]
    then fail $ "keyword " ++ show x ++ " cannot be an identifier"
    else return x
parens = between (symbol "(") (symbol ")")
squares = between (symbol "[") (symbol "]")
comma = symbol ","
lambda = symbol "\\"
dotP = symbol "->"
letP = symbol "let"
inP = symbol "in"
semi = symbol ";"
equals = symbol "="
ltermParser = foldl1 UApp <$> (some atomParser)
atomParser =
  (uvar <$> identifier)
    <|> numParser
    <|> listParser
    <|> letParser
    <|> lambdaParser
    <|> parens (ltermParser)
lambdaParser = mkLam <$> lambda <*> some identifier <*> dotP <*> ltermParser
  where mkLam _ ids _ t = foldr ulam t ids
letParser = mkLet <$> letP <*> sepBy bindingParser semi <*> inP <*> ltermParser
  --where mkLet _ bindings _ t = foldr (\(x,ui) v -> UApp (ulam x v) u) t bindings
 where
  mkLet _ bindings _ t =
    foldr (\(x, u) v -> U.subst (string2Name x) u v) t bindings
bindingParser = mkBinding <$> identifier <*> equals <*> ltermParser
  where mkBinding id _ t = (id, t)
numParser = mkNum <$> lexeme L.decimal
 where
  mkNum n = ulam "z" (ulam "s" (mkNum' n))
  mkNum' 0 = uvar "z"
  mkNum' n = UApp (uvar "s") (mkNum' (n - 1))
listParser = mkList <$> squares (ltermParser `sepBy` comma)
 where
  mkList xs = ulam "$n" (ulam "$c" (mkList' xs))
  mkList' []       = uvar "$n"
  mkList' (x : xs) = UApp (UApp (uvar "$c") x) (mkList' xs)

parseLTerm :: String -> Either (ParseError Char Dec) UTerm
parseLTerm s = parse (sc *> (ltermParser <* eof)) "" s

{- Evaluation -}

size (Var _    ) = 1
size (Lam t    ) = 1 + size t
size (App t1 t2) = size t1 + size t2

shift :: Int -> Int -> Term -> Term
shift c d (Var i) | i < c     = Var i
                  | otherwise = Var (i + d)
shift c d (Lam t    ) = Lam (shift (c + 1) d t)
shift c d (App t1 t2) = App (shift c d t1) (shift c d t2)

recLam v l a (Var i  ) = v i
recLam v l a (Lam t  ) = l t (recLam v l a t)
recLam v l a (App t u) = a t u (recLam v l a t) (recLam v l a u)

subst :: Int -> Term -> Term -> Term
subst i u (Var j) | i == j    = u
                  | otherwise = Var j
subst i u (Lam t    ) = Lam (subst (i + 1) (shift 0 1 u) t)
subst i u (App t1 t2) = App (subst i u t1) (subst i u t2)

apply :: Term -> Term -> Term
apply (Lam t) u = shift 0 (-1) (subst 0 (shift 0 1 u) t)
apply t       u = App t u

reduceOne :: Term -> Maybe Term
reduceOne (App t@(Lam _) u) = Just (apply t u)
reduceOne (App t u) = (flip App u <$> reduceOne t) <|> (App t <$> reduceOne u)
reduceOne (Lam t          ) = Lam <$> reduceOne t
reduceOne (Var x          ) = Nothing

reduceOneRmOm :: Term -> Maybe Term
reduceOneRmOm (App t@(Lam _) u) = Just (apply t u)
reduceOneRmOm (App t u) =
  (App t <$> reduceOne u) <|> (flip App u <$> reduceOne t)
reduceOneRmOm (Lam t) = Lam <$> reduceOne t
reduceOneRmOm (Var x) = Nothing

reduceOneLmIm :: Term -> Maybe Term
reduceOneLmIm (App t@(Lam _) u) =
  (flip App u <$> reduceOneLmIm t) <|> (App t <$> reduceOneLmIm u) <|> Just
    (apply t u)
reduceOneLmIm (App t u) =
  (flip App u <$> reduceOneLmIm t) <|> (App t <$> reduceOneLmIm u)
reduceOneLmIm (Lam t) = Lam <$> reduceOneLmIm t
reduceOneLmIm (Var _) = Nothing

reduceOneRmIm :: Term -> Maybe Term
reduceOneRmIm (App t@(Lam _) u) =
  (App t <$> reduceOneRmIm u) <|> (flip App u <$> reduceOneRmIm t) <|> Just
    (apply t u)
reduceOneRmIm (App t u) =
  (flip App u <$> reduceOneRmIm t) <|> (App t <$> reduceOneRmIm u)
reduceOneRmIm (Lam t) = Lam <$> reduceOneRmIm t
reduceOneRmIm (Var _) = Nothing

debug s t = Debug.Trace.trace (s ++ ": " ++ pretty t) False

reduceOneCbv' :: Term -> Maybe Term
--reduceOneCbv' u | debug "reduceOneCbv'" u = undefined
reduceOneCbv' (App t@(Lam _) u@(Lam _)) = Just (apply t u)
reduceOneCbv' (App t@(Lam _) u        ) = App t <$> reduceOneCbv' u
reduceOneCbv' (App t         u        ) = flip App u <$> reduceOneCbv' t
reduceOneCbv' (Lam _                  ) = Nothing
reduceOneCbv' (Var _                  ) = Nothing

reduceOneCbv t = go t
 where
  go t = case reduceOneCbv' t of
    Just t' -> Just t'
    Nothing -> deep t
--    deep u | debug "deep" u = undefined
  deep (Lam u) = Lam <$> deep u
  deep u       = (reduceOneCbv' u <|> reduceOneLmIm u)

reduceMany :: Term -> [Term]
reduceMany t =
  t
    : (case reduceOneLmIm t of
        Just t' -> reduceMany t'
        Nothing -> []
      )

{- Drawing -}

double :: Int -> Double
double = fromIntegral

vbar :: Int -> Diagram B
vbar n = vrule (double n) # alignT

hbar :: Int -> Diagram B
hbar n = hrule (double n) # alignL

draw :: Term -> Diagram B
draw t = let (fig, _, _) = draw' t in fig # lwL 0.5 # frame 1
 where
  draw' :: Term -> (Diagram B, Int, Int)
  draw' (Lam t) = (binder <> (fig # translateY (-1)), h + 1, w)
   where
    (fig, h, w) = draw' t
    binder      = hrule (double (2 * w) - 0.5) # alignL # translateX (-0.75)
  draw' (Var i) = (fig, 0, 1)
   where
    fig = (phantom (hrule 2 :: Diagram B) <> vrule (double $ i + 1)) # alignB
  draw' (App t1 t2) =
    (((fig1 <> tail1) ||| (fig2 <> tail2)) <> bar, h1 + delta1 + 1, w1 + w2)
   where
    (fig1, h1, w1) = draw' t1
    (fig2, h2, w2) = draw' t2
    delta1         = max 0 (h2 - h1)
    delta2         = max 0 (h1 - h2)
    tail1          = vbar (delta1 + 1) # translateY (double (-h1))
    tail2          = vbar delta2 # translateY (double (-h2))
    bar =
      hbar (2 * w1) # translateY (double (-h1 - delta1)) # lineCap LineCapSquare

{- Animation -}

tdims :: Term -> V2 Double
tdims t = V2 (fromIntegral $ twidth t) (fromIntegral $ theight t)
 where
  twidth t = 2 * (1 + twidth' t)
  twidth' (Lam t    ) = twidth' t
  twidth' (App t1 t2) = twidth' t1 + twidth' t2
  twidth' (Var _    ) = 1

  theight t = 2 * theight' t
  theight' (Lam t    ) = 1 + theight' t
  theight' (App t1 t2) = 1 + max (theight' t1) (theight' t2)
  theight' (Var _    ) = 0

_drawTerm t =
  (window # scaleUToX 80 # alignBR # translate (V2 160 (-90)))
    <> (fullTerm # scaleUToX 160)
    <> (background # alignTL)
 where
  fullTerm = draw t # alignTL
  window =
    (fullTerm # translate (V2 4 6) # alignTL # withEnvelope
        (rect 160 90 # alignTL :: Diagram B)
      )
      <> (rect 160 90 # bg white # alignTL # lc black)
  background = rect 160 90 # bg white

drawTerm t = draw t # bg white # alignTL

extents :: [Term] -> V2 Double
extents ts = foldl' vmax (V2 0 0) (map tdims ts)
 where
  imgs = map drawTerm ts
  vmax (V2 !w1 !h1) (V2 !w2 !h2) = V2 (max w1 w2) (max w2 h2)

images :: Term -> [Diagram B]
images t = map normalize imgs
 where
  ts       = reduceMany t
  imgs     = map drawTerm ts
  (V2 w h) = extents ts
  bgrect   = rect (w + 10) (h + 10) # fc white # lw 0 # alignTL
  --normalize img = (img <> bgrect)
  normalize img = img

_movie :: Term -> [Diagram B]
_movie t = replicate 50 (head imgs) ++ imgs where imgs = images t

{- Main -}

process :: (UTerm -> IO ()) -> IO ()
process f = do
  s <- getContents
  case parseLTerm s of
    Left  e  -> error (parseErrorPretty e)
    Right lt -> f lt


imgMain t = zipWithM_ render [0 :: Int ..] (_movie t)
 where
  render i img = renderRasterific (filePath i) size img
  filePath i = printf "/tmp/out_%04d.png" i
  --size = mkWidth 3840
  size = dims2D 1600 900

imgInputMain = process (imgMain . uterm2term)

evalMain :: Term -> IO ()
--evalMain t = mapM_ (putStrLn . pretty) (reduceMany t)
evalMain t = do
  let ts = reduceMany t
  print (length ts)
  print (extents ts)
  (putStrLn . pretty . last) ts

evalInputMain :: IO ()
evalInputMain = process (evalMain . uterm2term)

dbMain :: IO ()
dbMain = process (print . uterm2term)

cpsMain :: IO ()
cpsMain = process (putStrLn . pretty . uterm2term . runOcps)

main = do
  --cpsMain
  --dbMain
  --evalMain t
  --evalInputMain
  --imgMain t
  imgInputMain
