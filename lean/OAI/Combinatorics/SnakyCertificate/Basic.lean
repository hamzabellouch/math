import Mathlib

namespace OAI

namespace SnakyCertificate

instance rotationModulus_neZero : NeZero 8 := @Nat.instNeZeroSucc 7

instance digitModulus_neZero : NeZero 10 := @Nat.instNeZeroSucc 9

abbrev Cell := ℤ × ℤ

def origin : Cell := (0, 0)

def snaky : Finset Cell := {(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)}

def orient (r : Fin 8) (p : Cell) : Cell :=
  match r.val with
  | 0 => (p.1, p.2)
  | 1 => (p.2, p.1)
  | 2 => (p.1, -p.2)
  | 3 => (-p.2, p.1)
  | 4 => (-p.1, p.2)
  | 5 => (p.2, -p.1)
  | 6 => (-p.1, -p.2)
  | _ => (-p.2, -p.1)

def placement (r : Fin 8) (t p : Cell) : Cell := orient r p + t

def basePoint (i : Fin 6) : Cell := ![(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)] i

def baseEnvelope (i : Fin 6) : Finset Cell :=
  snaky.image (placement 0 (-basePoint i))

def baseRequired (i : Fin 6) : Finset Cell := (baseEnvelope i).erase origin

structure Term where
  child : ℕ
  rotation : Fin 8
  xDigit : Fin 10
  yDigit : Fin 10
  deriving DecidableEq, Repr

def Term.shift (t : Term) : Cell := ((t.xDigit.val : ℤ) - 4, (t.yDigit.val : ℤ) - 4)

structure Entry where
  index : ℕ
  terms : List Term
  deriving DecidableEq, Repr

def emptyEntry : Entry := ⟨0, []⟩

end SnakyCertificate

end OAI
