import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialDegenerationComposition
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialWitnessProduct
import Mathlib.Tactic.Ring

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

inductive Color where
  | B | A | C
  deriving DecidableEq

instance : Fintype Color where
  elems := {.B, .A, .C}
  complete color := by cases color <;> simp

structure FlaggedTensor (X Y Z : Type*) where
  tensor : Tensor ℂ X Y Z
  flagB : X → Prop
  flagA : Z → Prop
  flagC : Y → Prop
  one_hot : ∀ x y z, tensor x y z ≠ 0 →
    (if flagB x then 1 else 0) + (if flagA z then 1 else 0) +
      (if flagC y then 1 else 0) = (1 : ℕ)

namespace RecursiveCompletion

def raisedFlag {I : Type*} (center color : Color) (p : I → Prop) : Prop :=
  if center = color then ∀ i, p i else ∃ i, p i

variable {X Y Z : Type*}

def flagB (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (x : Fin m → X) : Prop := raisedFlag center .B (fun i => S.flagB (x i))

def flagA (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (z : Fin m → Z) : Prop := raisedFlag center .A (fun i => S.flagA (z i))

def flagC (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (y : Fin m → Y) : Prop := raisedFlag center .C (fun i => S.flagC (y i))

def weight (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (x : Fin m → X) (y : Fin m → Y) (z : Fin m → Z) : ℕ :=
  (if flagB S center m x then 1 else 0) +
    (if flagA S center m z then 1 else 0) +
    (if flagC S center m y then 1 else 0)

theorem weight_pos (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (x : Fin m → X) (y : Fin m → Y) (z : Fin m → Z)
    (hs : Tensor.power S.tensor m x y z ≠ 0) :
    0 < weight S center m x y z := by
  classical
  have hold (i : Fin m) :
      (if S.flagB (x i) then 1 else 0) +
        (if S.flagA (z i) then 1 else 0) +
        (if S.flagC (y i) then 1 else 0) = (1 : ℕ) := by
    apply S.one_hot
    exact (Finset.prod_ne_zero_iff.mp hs) i (Finset.mem_univ i)
  by_contra h
  have hw : weight S center m x y z = 0 := Nat.eq_zero_of_not_pos h
  have hb : ¬ flagB S center m x := by
    intro hb
    simp only [weight, ite_eq_left hb] at hw
    omega
  have ha : ¬ flagA S center m z := by
    intro ha
    simp only [weight, ite_eq_left ha] at hw
    omega
  have hc : ¬ flagC S center m y := by
    intro hc
    simp only [weight, ite_eq_left hc] at hw
    omega
  cases center with
  | B =>
      change ¬ (∀ i, S.flagB (x i)) at hb
      change ¬ (∃ i, S.flagA (z i)) at ha
      change ¬ (∃ i, S.flagC (y i)) at hc
      obtain ⟨i, hi⟩ := not_forall.mp hb
      simpa [hi, not_exists.mp ha i, not_exists.mp hc i] using hold i
  | A =>
      change ¬ (∃ i, S.flagB (x i)) at hb
      change ¬ (∀ i, S.flagA (z i)) at ha
      change ¬ (∃ i, S.flagC (y i)) at hc
      obtain ⟨i, hi⟩ := not_forall.mp ha
      simpa [not_exists.mp hb i, hi, not_exists.mp hc i] using hold i
  | C =>
      change ¬ (∃ i, S.flagB (x i)) at hb
      change ¬ (∃ i, S.flagA (z i)) at ha
      change ¬ (∀ i, S.flagC (y i)) at hc
      obtain ⟨i, hi⟩ := not_forall.mp hc
      simpa [not_exists.mp hb i, not_exists.mp ha i, hi] using hold i

def complete (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    FlaggedTensor (Fin m → X) (Fin m → Y) (Fin m → Z) where
  tensor x y z := if weight S center m x y z = 1 then
    Tensor.power S.tensor m x y z else 0
  flagB := flagB S center m
  flagA := flagA S center m
  flagC := flagC S center m
  one_hot := by
    intro x y z hs
    by_cases hw : weight S center m x y z = 1
    · exact hw
    · simp [hw] at hs

@[simp] theorem complete_tensor (S : FlaggedTensor X Y Z) (center : Color)
    (m : ℕ) (x : Fin m → X) (y : Fin m → Y) (z : Fin m → Z) :
    (complete S center m).tensor x y z =
      if weight S center m x y z = 1 then Tensor.power S.tensor m x y z else 0 := rfl

def diagonalMap {K U : Type*} [Zero K] [DecidableEq U] (f : U → K) : U → U → K :=
  fun output input => if input = output then f output else 0

theorem restrict_diagonal {K U V W : Type*} [CommSemiring K]
    [Fintype U] [Fintype V] [Fintype W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W]
    (a : U → K) (b : V → K) (c : W → K) (T : Tensor K U V W)
    (x : U) (y : V) (z : W) :
    Tensor.restrict (diagonalMap a) (diagonalMap b) (diagonalMap c) T x y z =
      a x * b y * c z * T x y z := by
  simp [Tensor.restrict, diagonalMap, ite_mul, mul_ite]

def flagPolynomial (p : Prop) : Polynomial ℂ := if p then Polynomial.X else 1

theorem flagPolynomial_eq (p : Prop) :
    flagPolynomial p = (Polynomial.X : Polynomial ℂ) ^ (if p then 1 else 0 : ℕ) := by
  classical
  by_cases hp : p <;> simp [flagPolynomial, hp]

theorem flagPolynomial_degree (p : Prop) : (flagPolynomial p).degree ≤ 1 := by
  classical
  by_cases hp : p <;> simp [flagPolynomial, hp]

variable [Fintype X] [Fintype Y] [Fintype Z]

def leftMap (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    (Fin m → X) → (Fin m → X) → Polynomial ℂ :=
  diagonalMap (fun x => flagPolynomial (flagB S center m x))

def middleMap (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    (Fin m → Y) → (Fin m → Y) → Polynomial ℂ :=
  diagonalMap (fun y => flagPolynomial (flagC S center m y))

def rightMap (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    (Fin m → Z) → (Fin m → Z) → Polynomial ℂ :=
  diagonalMap (fun z => flagPolynomial (flagA S center m z))

theorem diagonalMap_flag_degree {U : Type*} [DecidableEq U] (p : U → Prop)
    (u v : U) : (diagonalMap (fun u => flagPolynomial (p u)) u v).degree ≤ 1 := by
  classical
  by_cases h : v = u
  · simpa [diagonalMap, h] using flagPolynomial_degree (p u)
  · simp [diagonalMap, h]

theorem scalingPolynomial (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (x : Fin m → X) (y : Fin m → Y) (z : Fin m → Z) :
    Tensor.restrict (leftMap S center m) (middleMap S center m) (rightMap S center m)
      (fun x y z => Polynomial.C (Tensor.power S.tensor m x y z)) x y z =
      Polynomial.C (Tensor.power S.tensor m x y z) *
        Polynomial.X ^ weight S center m x y z := by
  classical
  rw [leftMap, middleMap, rightMap, restrict_diagonal]
  simp only [flagPolynomial_eq, weight, pow_add]
  ring

def completionDegeneration (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (Tensor.power S.tensor m)
      (complete S center m).tensor 1 1 1 1 where
  leftMap := leftMap S center m
  middleMap := middleMap S center m
  rightMap := rightMap S center m
  left_degree := diagonalMap_flag_degree _
  middle_degree := diagonalMap_flag_degree _
  right_degree := diagonalMap_flag_degree _
  vanishes := by
    intro x y z j hj
    have hj0 : j = 0 := by omega
    subst j
    rw [scalingPolynomial, Polynomial.coeff_C_mul_X_pow]
    by_cases hs : Tensor.power S.tensor m x y z = 0
    · simp [hs]
    · have hw := weight_pos S center m x y z hs
      simp [Ne.symm (Nat.ne_of_gt hw)]
  leading := by
    intro x y z
    rw [scalingPolynomial, Polynomial.coeff_C_mul_X_pow, complete_tensor]
    simp only [eq_comm]

end RecursiveCompletion
end MatrixMultiplication

end

end OAI
