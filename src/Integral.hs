{-# LANGUAGE DeriveDataTypeable #-}
module Integral where


import Data.Typeable
import Data.Data

--some shortcuts
a :: Fraction
a = Frac 2 5
b :: Fraction
b = Frac 3 4
c :: Fraction
c = Frac (-2) 3
d :: Monomial
d = Mono 1 x 1
e :: Monomial
e = Mono 1 x 2
f :: Monomial
f = Mono (-2) x 3
fcos :: Monomial
fcos = Cos 1 x 1
fsin :: Monomial
fsin = Sin 1 x 1
flippy :: Monomial
flippy = derive (Mult fsin fsin)
dfcos2 :: Monomial
dfcos2 = derive (Mult fcos fcos)
ff :: Monomial
ff = Mono 3 x (Frac 1 3)
g :: Monomial
g = Poly [e,f,e]
h :: Monomial
h = Poly [ff]
x :: Monomial
x = Var 'x'
y :: Monomial
y = Var 'y'         

--Return the string representation of a monomial's constructor
kind :: Monomial -> String
kind = show . toConstr

--Return an empty constructor of the same kind as the input
same :: Monomial -> Fraction -> Monomial -> Fraction -> Monomial
same = readF . kind

--Is the input any of the trigonometric functions?
isTrig a = elem (kind a) ["Sin", "Cos", "Tan", "Sec", "Csc", "Cot"]

lookM :: Monomial -> (String, Fraction, Monomial, Fraction)
lookM x = (kind x, multiple x, term x, power x)
lookS :: Monomial -> (String, Monomial, Monomial)
lookS x = (kind x, first x, second x)

data Fraction = Frac {num :: Integer, denom :: Integer}
    deriving (Typeable, Data)

instance Show Fraction where
    show (Frac a 1) = show a
    show (Frac a b) = "(" ++ show a ++ "/" ++ show b ++ ")"

instance Num Fraction where
    (+) (Frac a b) (Frac c d)        = simplify (Frac (a*d + b*c) (b*d))
    (-) (Frac a b) (Frac c d)        = Frac a b + Frac (-c) d
    (*) (Frac a b) (Frac c d)        = simplify (Frac (a*c) (b*d))
    negate (Frac a b)                = Frac (-a) b
    abs (Frac a b)                   = Frac (abs a) (abs b)
    fromInteger x                    = Frac x 1
    signum (Frac 0 _)                = 0
    signum (Frac a b)                = if signum a == signum b then 1  else (-1)

instance Fractional Fraction where
    (/) f g          = f * recip g
    recip (Frac a b) = Frac b a                

instance Eq Fraction where
    Frac a b == Frac c d = a == c && b == d

instance Ord Fraction where
    compare (Frac a b) (Frac c d) = compare (a*d) (c*b)

simplify :: Fraction -> Fraction
simplify (Frac a b) = signAdjust(Frac (quot a factor) (quot b factor)) where
    factor = gcd a b

--move sign to the numerator, if needed, and simplify duplicate minus signs
signAdjust :: Fraction -> Fraction
signAdjust (Frac 0 b) = Frac 0 b
signAdjust (Frac a b) = if signum b == (-1) then Frac (-a) (-b) else Frac a b

data Monomial         = 
    Mono {multiple :: Fraction, term :: Monomial, power :: Fraction}
    | Var {variable :: Char}
    | Mult {first :: Monomial, second :: Monomial}
    | Sum {first :: Monomial, second :: Monomial}
    | Poly [Monomial]
    | Exp {multiple :: Fraction, term :: Monomial}
    | Ln {multiple :: Fraction, term :: Monomial, power :: Fraction}
    | Sin {multiple :: Fraction, term :: Monomial, power :: Fraction}
    | Cos {multiple :: Fraction, term :: Monomial, power :: Fraction}
    | Tan {multiple :: Fraction, term :: Monomial, power :: Fraction}
    | Sec {multiple :: Fraction, term :: Monomial, power :: Fraction}
    | Csc {multiple :: Fraction, term :: Monomial, power :: Fraction}
    | Cot {multiple :: Fraction, term :: Monomial, power :: Fraction}
    deriving (Typeable, Data)
        --deriving (Typeable, Data)

instance Num Monomial where
    (+) 0 b = b
    (+) a 0 = a        
    (+) m1@(Mono a x n) m2@(Mono b y o)
        | x == y && n == o = Mono (a+b) x n
        | otherwise = Sum m1 m2
    (+) m1@(Mult a b) m2@(Mult c d)
        | m1 == m2 = Mono 2 (Mult a b) 1
        | otherwise = Sum m1 m2
    (+) a b                                
        -- | a == b = Mono 2 ((same a) (term a) (power a)) 1
        | a == (-b) = 0
        | kind a == "Mono" && term a == b && power a == 1 = Mono (multiple a + 1) b 1 --a is a Mono containing several b
        | kind b == "Mono" && term b == a && power b == 1 = Mono (multiple b + 1) a 1 --b is a Mono containing several a
        | otherwise = Sum a b
    (-) a b = a + (-b)
    (*) 1 b = b
    (*) a 1 = a
    (*) 0 _ = 0
    (*) _ 0 = 0
    (*) x@(Var v) a = Mono 1 x 1 * a
    (*) a x@(Var v) = a * Mono 1 x 1
    (*) m1@(Mono a x n) m2@(Mono b y o)
        | x == y || n == 0 || o == 0 = Mono (a*b) x (n+o)
        | otherwise = Mult m1 m2
    (*) m1@(Mono a _ 0) (Exp b x) = Exp (a*b) x
    (*) (Exp a x) m2@(Mono b _ 0) = Exp (a*b) x

    --scalar * function (except exp)
    (*) m1@(Mono a _ 0) b         = (same b) (a * multiple b) (term b) (power b) 
    (*) a m1@(Mono b _ 0)         = (same a) (b * multiple a) (term a) (power a)
        
    (*) m1@(Mult a b) m2@(Mult c d)
        | m1 == m2 = Mono 1 (Mult a b) 2
        | otherwise = Mult m1 m2
    (*) (Exp a x) (Exp b y) = Exp (a*b) (x+y)
    (*) a b
        | kind a == kind b && term a == term b = (same a) (multiple a * multiple b) (term a) (power a + power b)
        | otherwise = Mult a b
    negate (Mono a x n) = Mono (-a) x n
    negate (Poly l)     = Poly (map negate l)
    negate (Sum a b)    = (-a) + (-b)
    negate a
        | kind a == "Exp"              = Exp (-multiple a) (term a)
        | kind a == "Ln"               = Ln (-multiple a) (term a) (power a)
        | isTrig a                     = (same a) (-multiple a) (term a) (power a)
        | otherwise                    = Mono (Frac (-1) 1) a (Frac 1 1)
    abs (Mono a x n)    = Mono (abs a) x n
    abs other           = other
    fromInteger x       = Mono (Frac x 1) (Var 'x') (Frac 0 1)
    signum (Mono a _ _) = Mono (signum a) (Var 'x') (Frac 0 1)
    signum _            = 1

--instance Fractional Monomial where
--    (/) f g = Mono f g (-1)
--    recip a = Mono 1 a (-1)

instance Eq Monomial where
    Mono 0 _ _ == Mono 0 _ _ = True
    Mono a _ 0 == Mono b _ 0 = a == b
    Mono a x n == Mono b y o = a == b && x == y && n == o
    Mono 0 _ _ == Sum a b    = a == 0 && b == 0
    Sum a b == Mono 0 _ _    = a == 0 && b == 0
    Sum a b == Sum c d       = (a == c && b == d) || (a == d && b == c)
    Mult a b == Mult c d     = (a == c && b == d) || (a == d && b == c)
    Exp a x == Exp b y       = a == b && x == y
    Ln a x n == Ln b y o     = a == b && x == y && n == o
    Sin a x n == Sin b y o   = a == b && x == y && n == o
    Cos a x n == Cos b y o   = a == b && x == y && n == o
    Tan a x n == Tan b y o   = a == b && x == y && n == o
    Sec a x n == Sec b y o   = a == b && x == y && n == o
    Csc a x n == Csc b y o   = a == b && x == y && n == o
    Cot a x n == Cot b y o   = a == b && x == y && n == o
    Var x == Var y           = x == y
    _ == _                   = False

instance Ord Monomial where
    compare (Mono a x n) (Mono b y o) = compare a b

instance Show Monomial where
    show (Mono 0 _ _)        = show 0
    show (Mono a _ 0)        = show a
    show (Mono a (Var x) n)  = if n > 0
        then show' a ++ [x] ++ showPow n
        else show a ++ "/" ++ [x] ++ showPow (-n)
    show (Mono a x n)        = if n > 0
        then show' a ++ "(" ++ show x ++ ")" ++ showPow n
        else show a ++ "/(" ++ show x ++ ")" ++ showPow (-n)
    show (Var x)             = [x]
    show (Mult x1 x2)        = "(" ++ show x1 ++ " * " ++ show x2 ++ ")"
    show (Sum x1 x2)         = if (signum x2) >= 0
        then "(" ++ show x1 ++ " + " ++ show x2 ++ ")"
        else "(" ++ show x1 ++ " - " ++ show (-x2) ++ ")"
    show (Poly (x:[]))       = show x
    show (Poly (x:xs))       = show x ++ " " ++ sign' sign'' ++ show (Poly xs) where
        sign' "1" = "+"
        sign' _ = ""
        sign''  = (show . sign . head) xs
    show (Exp a v@(Var x))   = show' a ++ "e^" ++ show v
    show (Exp a x)           = show' a ++ "e^(" ++ show x ++ ")"
    show (Ln a x n)          = showFunc "ln" a x n
    show (Cos a x n)         = showFunc "cos" a x n
    show (Sin a x n)         = showFunc "sin" a x n
    show (Tan a x n)         = showFunc "tan" a x n
    show (Sec a x n)         = showFunc "sec" a x n
    show (Csc a x n)         = showFunc "csc" a x n
    show (Cot a x n)         = showFunc "cot" a x n

readF :: String -> Fraction -> Monomial -> Fraction -> Monomial
readF "Ln" = Ln
readF "Sin" = Sin
readF "Cos" = Cos
readF "Tan" = Tan
readF "Sec" = Sec
readF "Csc" = Csc
readF "Cot" = Cot
readF _ = Mono

showFunc :: String -> Fraction -> Monomial -> Fraction -> String
showFunc name a x n = show' a ++ name ++ showPow n ++ maybeParens x where
    maybeParens x = case (kind x) of
        "Mult"  -> show x
        "Sum"   -> show x
        _       -> "(" ++ show x ++ ")"

show' :: Fraction -> String
show' a = case a of
    (-1) -> "-"
    1 -> ""
    _ -> (show . simplify) a
showPow :: Fraction -> String
showPow n = case n of
    1 -> ""
    _ -> "^" ++ (show . simplify) n

sign :: Monomial -> Fraction
sign (Mono a _ _) = signum a
sign _            = 1


derive :: Monomial -> Monomial
derive (Var x)                  = Mono 1 (Var x) 0
derive (Mono _ x 0)             = Mono 0 x 0
derive (Mono a (Var x) n)       = Mono (a*n) (Var x) (n-1)
derive (Mono a x n)             = Mono (a*n) x (n-1) * derive x
derive (Exp a x)                = Exp a x * derive x
derive (Ln a x 1)               = Mono a x (-1) * derive x 
derive (Sin a x 1)              = Cos a x 1 * derive x
derive (Cos a x 1)              = Sin (-a) x 1 * derive x
derive (Tan a x 1)              = Sec a x 2 * derive x
derive (Sec a x 1)              = Tan a x 1 * derive x * Sec 1 x 1
derive (Csc a x 1)              = Cot (-a) x 1 * derive x * Csc 1 x 1
derive (Cot a x 1)              = Csc (-a) x 2 * derive x
derive (Sum x1 x2)              = (derive x1) + (derive x2)
derive (Mult x1 x2)             = (derive x1) * x2 + x1 * (derive x2)
derive (Poly l)                 = Poly (map derive l)

integrate :: Monomial -> Monomial
integrate (Var x)                   = Mono (Frac 1 2) (Var x) 2
integrate (Mono a (Var x) (-1))     = Ln a (Var x) 1
integrate (Mono a x n)              = Mono (a/(n+1)) x (n+1)
integrate (Ln a x 1)                = x * (Ln a x 1) - x
integrate (Sin a (Var x) 1)         = Cos (-a) (Var x) 1
integrate (Sin a t@(Mono b x 1) 1)  = Cos (-a/b) t 1
integrate (Cos a (Var x) 1)         = Sin a (Var x) 1
integrate (Cos a t@(Mono b x 1) 1)  = Sin (a/b) t 1
integrate (Tan a (Var x) 1)         = Ln (-a) (Cos 1 (Var x) 1) 1
integrate (Tan a t@(Mono b x 1) 1)  = Ln (-a/b) (Cos 1 t 1) 1
integrate (Cot a (Var x) 1)         = Ln a (Sin 1 (Var x) 1) 1
integrate (Cot a t@(Mono b x 1) 1)  = Ln (a/b) (Sin 1 t 1) 1
--integrate (Sin a (Var x) 1)         = Cos (-a) (Var x) 1
--integrate (Sin a t@(Mono b x 1) 1)  = Cos (-a/b) t 1
--integrate (Sin a (Var x) 1)         = Cos (-a) (Var x) 1
--integrate (Sin a t@(Mono b x 1) 1)  = Cos (-a/b) t 1
integrate (Mult a b)                = a * integrate b - integrate (derive a * integrate b) --this works. wow.
integrate (Sum a b)                 = integrate a + integrate b
integrate (Poly l)                  = Poly (map integrate l)

{--
simpM :: Monomial -> Monomial
--simpM (Mono a (Mono b y o) n) =
simpM (Mono 1 x 1) = x
simpM (Mult m1@(Mono a x n) m2@(Mono b y o)) =
        if x == y then Mono (a*b) x (n+o) else Mult m1 m2
simpM (Mult m1@(Mono a x 0) m2) = Mono a (simpM m2) 1
simpM (Mult m1 m2@(Mono a x 0)) = Mono a (simpM m1) 1
simpM (Mult m1 m2) =
        if toConstr m1 == toConstr m2 then (same m1) (term m1) (power m1 + power m2) else Mult m1 m2 where
        
simpM (Sum m1@(Mono a x n) m2@(Mono b y o)) =
        if x == y && n == o then Mono (a+b) x n else Sum m1 m2
simpM (Sum m1 m2) =
        if toConstr m1 == toConstr m2 && power m1 == power m2 && term m1 == term m2
        then Mono 2 m1 1
        else Sum m1 m2
simpM other = other

--}
{--
data Polynomial = Poly [Monomial]
                                | Var Char

        deriving (Typeable, Data)

instance Show Polynomial where
        show (Var x) = id [x]
        show (Poly (x:[])) = show x
        show (Poly (x:xs)) = show x ++ " " ++ sign' sign'' ++ show (Poly xs) where
                sign' "1" = "+"
                sign' _ = ""
                sign''  = (show . sign . head) xs

derive :: Polynomial -> Polynomial
derive (Poly l) = Poly (map deriv' l)

deriv' :: Monomial -> Monomial
deriv' (Mono a x 0) = Mono 0 x 0
deriv' (Mono a x n) = Mono (a*n) x (n-1)
deriv' (Func (Cos a x 1)) = Func (Sin (-a) x 1)
deriv' (Func (Sin a x 1)) = Func (Cos a x 1)
deriv' (Func (Tan a x 1)) = Func (Sec a x 2)
deriv' (Func (Cot a x 1)) = Func (Csc (-a) x 2)
deriv' (Mult a b) = Sum (Mult a (deriv' b)) (Mult (deriv' a) b)

integrate :: Polynomial -> Polynomial
integrate (Poly l) = Poly (map integ' l)

integ' :: Monomial -> Monomial
integ' (Mono a x (-1))        = Func (Ln a (Poly [Mono 1 x 1]) 1)
integ' (Mono a x n)                = Mono (a/(n+1)) x (n+1)

--S udv = uv - S duv
integByParts :: Monomial -> Polynomial
integByParts (Mult a b) = Poly [Mult a (integ' b), Mult (deriv' a) (integ' b)]
--}

{--
derive (Mono a (Ln x 1) 1)        = (Mono a x (-1)) * (derive x) --not quite
derive (Mono a (Cos x 1) 1)        = (Mono (-a) (Sin x 1) 1) * (derive x)
derive (Mono a (Sin x 1) 1)        = (Mono a (Cos x 1) 1) * (derive x)
derive (Mono a (Tan x 1) 1)        = (Mono a (Sec x 2) 1) * (derive x)
derive (Mono a (Sec x 1) 1)        = (Mono a (Mult (Tan x 1) (Sec x 1)) 1) * (derive x)
derive (Mono a (Csc x 1) 1)        = (Mono (-a) (Mult (Cot x 1) (Csc x 1)) 1) * (derive x)
derive (Mono a (Cot x 1) 1)        = (Mono (-a) (Csc x 2) 1) * (derive x)
derive (Mono a x n)                 = (Mono (a*n) x (n-1)) * (derive x)
derive (Sum x1 x2)                         = (derive x1) + (derive x2)
derive (Mult x1 x2)                        = (derive x1) * x2 + x1 * (derive x2)
derive (Exp x)                                = (Exp x) * (derive x)
derive (Ln x 1)                         = (Mono 1 x (-1)) * (derive x) --not quite
derive (Cos x 1)                         = (Mono (-1) (Sin x 1) 1) * (derive x)
derive (Sin x 1)                         = (Cos x 1) * (derive x)
derive (Tan x 1)                         = (Sec x 2) * (derive x)
derive (Sec x 1)                         = (Mult (Tan x 1) (Sec x 1)) * (derive x)
derive (Csc x 1)                         = (Mult (Cot x 1) (Mono (-1) (Csc x 1) 1)) * (derive x)
derive (Cot x 1)                         = (Mono (-1) (Csc x 2) 1) * (derive x)
derive (Poly l)                         = simpM $ Poly (map derive l)
--}
