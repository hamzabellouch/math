import OAI.Combinatorics.ContingencyTables.Rooted.ForestAffineProgram

namespace OAI

/-! # Binary signed arithmetic used to prepare the forest evaluator

A pair stores a difference of naturals. Arithmetic never iterates through
the represented integer value, and normalization returns the exact
positive/negative parts expected by the affine penalty program.
-/

namespace ContingencyTables.SignedPairProgram

open MatchingFPRAS.TreeTyped
open scoped BigOperators

abbrev Signed := ℕ×ℕ

def value (a : Signed) : ℤ := (a.1:ℤ)-a.2

def plus (z : Signed×Signed) : Signed := (z.1.1+z.2.1,z.1.2+z.2.2)
def neg (a : Signed) : Signed := (a.2,a.1)
def minus (z : Signed×Signed) : Signed := plus (z.1,neg z.2)
def times (z : Signed×Signed) : Signed :=
  (z.1.1*z.2.1+z.1.2*z.2.2,z.1.1*z.2.2+z.1.2*z.2.1)
def normalize (a : Signed) : Signed := (a.1-a.2,a.2-a.1)

lemma value_plus (a b : Signed) : value (plus (a,b))=value a+value b := by
  simp only [value,plus,Nat.cast_add]
  ring

lemma value_neg (a : Signed) : value (neg a)= -value a := by
  unfold value neg
  ring

lemma value_minus (a b : Signed) : value (minus (a,b))=value a-value b := by
  rw [minus,value_plus,value_neg]
  ring

lemma value_times (a b : Signed) : value (times (a,b))=value a*value b := by
  simp only [value,times,Nat.cast_add,Nat.cast_mul]
  ring

lemma normalize_eq (a : Signed) : normalize a=ForestAffineProgram.signedParts (value a) := by
  rcases a with ⟨p,q⟩
  apply Prod.ext <;> simp only [normalize,ForestAffineProgram.signedParts,value]
  · omega
  · omega

lemma value_normalize (a : Signed) : value (normalize a)=value a := by
  rw [normalize_eq]
  exact ForestAffineProgram.signedParts_sub (value a)

def plusRealizer : Realizer plus :=
  pair
    (composition (pair (composition first first) (composition second first)) add)
    (composition (pair (composition first second) (composition second second)) add)

def negRealizer : Realizer neg := pair second first

def minusRealizer : Realizer minus :=
  composition (pair first (composition second negRealizer)) plusRealizer

def timesRealizer : Realizer times :=
  pair
    (composition (pair
      (composition (pair (composition first first) (composition second first)) multiply)
      (composition (pair (composition first second) (composition second second)) multiply)) add)
    (composition (pair
      (composition (pair (composition first first) (composition second second)) multiply)
      (composition (pair (composition first second) (composition second first)) multiply)) add)

def normalizeRealizer : Realizer normalize :=
  pair subtract (composition (pair second first) subtract)

lemma polynomial_plus : PolynomialTime plusRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition polynomial_second polynomial_first)) polynomial_add)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_add)

lemma polynomial_neg : PolynomialTime negRealizer :=
  polynomial_pair polynomial_second polynomial_first

lemma polynomial_minus : PolynomialTime minusRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_neg)) polynomial_plus

lemma polynomial_times : PolynomialTime timesRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first)
        (polynomial_composition polynomial_second polynomial_first)) polynomial_multiply)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_second)
        (polynomial_composition polynomial_second polynomial_second)) polynomial_multiply)) polynomial_add)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first)
        (polynomial_composition polynomial_second polynomial_second)) polynomial_multiply)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_second)
        (polynomial_composition polynomial_second polynomial_first)) polynomial_multiply)) polynomial_add)

lemma polynomial_normalize : PolynomialTime normalizeRealizer :=
  polynomial_pair polynomial_subtract
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_subtract)

def sum (xs : List Signed) : Signed := ((xs.map Prod.fst).sum,(xs.map Prod.snd).sum)

def sumRealizer : Realizer sum :=
  pair (composition (map first) listSum) (composition (map second) listSum)

lemma polynomial_sum : PolynomialTime sumRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_map polynomial_first) polynomial_listSum)
    (polynomial_composition (polynomial_map polynomial_second) polynomial_listSum)

lemma value_sum (xs : List Signed) : value (sum xs)=(xs.map value).sum := by
  induction xs with
  | nil => simp [sum,value]
  | cons a xs ih =>
    simp only [sum,List.map_cons,List.sum_cons,value,Nat.cast_add] at *
    rw [←ih]
    ring

end ContingencyTables.SignedPairProgram

end OAI
