import Mathlib

namespace OAI

namespace BinomialDimension
irreducible_def binomialDimension (q : ℕ) : ℕ := Nat.choose q 8
def Q := (Nat.choose 1027 513)^3
def L := binomialDimension Q
lemma L_def : L=Nat.choose Q 8 := binomialDimension_def Q
def D := 4^L

end BinomialDimension

end OAI
