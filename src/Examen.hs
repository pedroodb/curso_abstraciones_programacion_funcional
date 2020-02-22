{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

{-
EXAMEN
"Abstracciones en la Práctica de la Programación Funcional"
RIO 2020
por Mauro Jaskelioff

Resolver los ejercicios en este archivo. y
enviar la solución por correo electrónico a:

mauro @ fceia.unr.edu.ar

antes del 7/3/2020.
-}

module Examen where

import Prelude hiding ((<>),mempty,Monoid)

import Monoid
import Functors
import Generics
import Applicative
import Alternative hiding (expr,term,factor)
import Control.Applicative

-------------------------------------
-- Monoides
-------------------------------------

{-  #1
 Definir una instancia válida de Monoid para el siguiente tipo de datos tal que
 su operación binaria calcule el mínimo entre sus argumentos.
-}

data Min a = Infinito | N a
  deriving Show

instance Ord a => Monoid (Min a) where
  mempty = Infinito
  Infinito <> ma = ma
  ma <> Infinito = ma
  (N a) <> (N b) = N (min a b)

-- Ayuda: En la instancia requerir que el tipo a sea ordenado (Ord a)

{- #2
 Definir un tipo de datos Max y definir una instancia de Monoid para el mismo
 tal que su operación binaria calcule el máximo entres sus argumentos.
-}

data Max a = NegInfinito | N' a
  deriving Show

instance Ord a => Monoid (Max a) where
  mempty = NegInfinito
  NegInfinito <> ma = ma
  ma <> NegInfinito = ma
  (N' a) <> (N' b) = N' (max a b)

-------------------------------------
-- Funtores
-------------------------------------

{- #3
 De ser posible, definir una instancia de Functor válida
 para el siguiente tipo de datos
-}

data CSList a = Vacia | Singleton a | ConsSnoc a (CSList a) a
  deriving Show

instance Functor CSList where
  fmap f Vacia = Vacia
  fmap f (Singleton x) = Singleton (f x)
  fmap f (ConsSnoc x csl y) = ConsSnoc (f x) (fmap f csl) (f y)

-----------------------------------------
-- Generics
-----------------------------------------

{- #4
 Dar una instancia de Generic para CSList
-}

instance Generic CSList where
  type Rep CSList = (K ()) :+: Id :+: (Id :*: CSList :*: Id)

  toRep Vacia = Inl (K ())
  toRep (Singleton x) = Inr (Inl (Id x))
  toRep (ConsSnoc x csl y) = Inr $ Inr $ FunProd (Id x) (FunProd csl (Id y))

  fromRep (Inl (K ())) = Vacia
  fromRep (Inr (Inl (Id x))) = Singleton x
  fromRep (Inr (Inr (FunProd (Id x) (FunProd csl (Id y))))) = ConsSnoc x csl y

{- #5
Usando crush (del módulo Generics) definir una función que calcule en
forma genérica el máximo y el mínimo almacenados en una estructura
(ver ejercicios #1 y #2).

Ejemplos:
> minmax [2,6,3]
(2,6)

> minmax (Node (Leaf 5) (Node (Leaf 3) (Leaf 4)))
(3,5)

> minmax (ConsSnoc 4 (Singleton 9) 7)
(4,9)

(Para que funcionen los ejemplos de más arriba es necesario
 que estén definidas instancias de Crush para [], Bin, y CSList)

 Por ejemplo:
-}

{- 

Comentado para evitar conflictos con la definicion anterior

instance Crush [] where
  gcrush = gcrush . toRep

-}

instance (Crush f) => Crush (Rec f) where
  gcrush (Rec t) = gcrush t

instance Crush Bin where
  gcrush = gcrush . toRep


instance Crush CSList where
  gcrush = gcrush . toRep

{-
No se especifica que hace minmax para estructuras vacías:
> minmax []
LAUNCHING MISSILE! EVACUATE EARTH.
-}

-- (Puntos extra si minmax calcula el resultado en una sola pasada)

instance (Monoid a, Monoid b) => Monoid (a, b) where
  mempty = (mempty, mempty)
  (ma, mb) <> (ma', mb') = (ma <> ma', mb <> mb')


getMinMax :: (Min a, Max b) -> (a,b)
getMinMax (N x, N' y) = (x,y)
-- En caso de querer definir la funcion minmax para functores vacios, deberia definir:
getMinMax (Infinito, NegInfinito) = undefined

minmax :: (Functor f, Generic f, Crush (Rep f), Ord a) => f a -> (a,a)
minmax fa = (getMinMax . gcrush . toRep $ (\x -> (N x, N' x)) <$> fa)

-- Ejemplos
ej51 = minmax [2,6,3]

ej52 = minmax (Node (Leaf 5) (Node (Leaf 3) (Leaf 4)))

ej53 = minmax (ConsSnoc 4 (Singleton 9) 7)

-----------------------------------------
-- Applicative / Alternative
-----------------------------------------

{- #6
  Dado un aplicativo f y un aplicativo g, es
  (f :+: g) un aplicativo?
  Dar la instancia o argumentar por qué no lo es.


  (f :+: g) no es un aplicativo, ya que:

    1) Para poder definir <*> tendria que poder definir:
      - Inr fab <*> Inr fa = Inr (fab <*> fa)
      - Inl gab <*> Inl ga = Inl (gab <*> ga)
      - Inr fab <*> Inl ga; que no puedo definir ya que f y g son aplicativos distintos
      - Inl gab <*> Inl ga; idem caso anterior
    2) Para definir pure x, deberia devolver algo del tipo (f :+: g), por lo que deberia 
    conocer los constructores del functor f o el functor g, y elegir construir uno u otro

-}

{- #7
Chequear que una cadena de paréntesis está bien balanceada con un parser

parentesis :: Parser ()

Por ejemplo
> parse parentesis  "(()())()"
Just ((),"")

> parse parentesis  "(()()()"
Nothing
-}

parentesis :: AppParser p => p ()
parentesis = parentesis' *> eof

parentesis' :: AppParser p => p ()
parentesis' = many parentesis'' *> pure ()

parentesis'' :: AppParser p => p ()
parentesis'' = (char '(') *> parentesis' <* (char ')')


ej71 = parse parentesis "(()())()"
ej72 = parse parentesis "(()()()"

{- #8
Evaluador de expresiones aritméticas

Dada la gramática BNF de expresiones aritméticas

  expr ::= term (’+’ expr | ε )
  term ::= factor (’*’ term | ε )
  factor ::= nat | ’(’ expr ’)’

(donde ε denota la cadena vacía y nat es un número natural)

Dar una función

  evalExpr :: String -> Maybe Int

que parsee expresiones y las evalúe.

Por ejemplo:

  > evalExpr "2*3+4*(1+4)"
Just 26

Recomendamos definir un parser para cada no terminal.

Puntos extra: Extender el parser para manejar resta y división.

-}


expr :: AppParser p => p Int
expr = ((+) <$> term <* (token (char '+')) <*> expr) <|> term

term :: AppParser p => p Int
term = ((*) <$> factor <* (token (char '*')) <*> term) <|> factor

factor :: AppParser p => p Int
factor = (token (char '(')) *> expr <* (token (char ')')) <|> nat

evalExpr str = fst <$> parse expr str

ej81 = evalExpr "2*3+4*(1+4)"
