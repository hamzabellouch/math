import OAI.Analysis.Quasitrace.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Data.Matrix.Basis

namespace OAI

/-! Corner-compatible two-quasitraces on the usual CStarMatrix algebra and the fixed-pair counterexample proposition. -/

section

noncomputable section
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

def upperLeft (a : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix fun i j => if i = 0 ∧ j = 0 then a else 0

/-- The extension is a 1-quasitrace, not a normalized 1-quasitrace. -/
def OneQuasitrace.IsTwo (τ : OneQuasitrace A) : Prop :=
  ∃ σ : OneQuasitrace (CStarMatrix (Fin 2) (Fin 2) A), ∀ a, σ (upperLeft a) = τ a

/-- Positivity via an adjoint square is equivalent to C*-positivity;
the norm bound is the actual contraction condition. -/
def PositiveContraction (a : A) : Prop := (∃ x, a = star x * x) ∧ ‖a‖ ≤ 1

def MainTarget : Prop :=
  ∃ (A : Type) (inst : CStarAlgebra A),
    letI := inst
    TopologicalSpace.SeparableSpace A ∧
    (∃ τ : OneQuasitrace A, τ.Normalized ∧ τ.IsTwo) ∧
    ∃ a b : A, PositiveContraction a ∧ PositiveContraction b ∧
      ∀ τ : OneQuasitrace A, τ.Normalized → τ.IsTwo →
        (1 : ℝ) / 144 ≤ (τ (a+b) - τ a - τ b).re

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A n : Type*} [CStarAlgebra A] [Fintype n] [DecidableEq n]

/-- A single matrix entry with the C*-matrix norm. -/
def entry (i j : n) (a : A) : CStarMatrix n n A := CStarMatrix.ofMatrix (Matrix.single i j a)
def corner (i : n) (a : A) : CStarMatrix n n A := entry i i a
def diagonal (a : n → A) : CStarMatrix n n A := CStarMatrix.ofMatrix (Matrix.diagonal a)

omit [Fintype n] in
@[simp] theorem entry_star (i j : n) (a : A) :
    star (entry i j a) = entry j i (star a) := by
  change (Matrix.single i j a).conjTranspose = Matrix.single j i (star a)
  exact Matrix.conjTranspose_single i j a

@[simp] theorem entry_mul (i j k : n) (a b : A) :
    entry i j a * entry j k b = entry i k (a * b) := by
  change Matrix.single i j a * Matrix.single j k b = Matrix.single i k (a * b)
  simp

omit [Fintype n] in
@[simp] theorem corner_star (i : n) (a : A) : star (corner i a) = corner i (star a) := entry_star i i a
@[simp] theorem corner_mul (i : n) (a b : A) : corner i a * corner i b = corner i (a*b) := entry_mul i i i a b

omit [Fintype n] in
theorem corner_selfAdjoint (i : n) {a : A} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (corner i a) := by
  change star (corner i a) = corner i a
  rw [corner_star, ha.star_eq]

theorem corner_commute {i j : n} (hij : i ≠ j) (a b : A) :
    Commute (corner i a) (corner j b) := by
  change Matrix.single i i a * Matrix.single j j b = Matrix.single j j b * Matrix.single i i a
  rw [Matrix.single_mul_single_of_ne a i i j hij b,
    Matrix.single_mul_single_of_ne b j j i hij.symm a]

theorem diagonal_eq_sum (a : n → A) : diagonal a = ∑ i, corner i (a i) := by
  change Matrix.diagonal a = ∑ i, Matrix.single i i (a i)
  exact (Matrix.sum_single_eq_diagonal a).symm

theorem corner_square_swap (τ : OneQuasitrace (CStarMatrix n n A)) (i : n) (x : A) :
    τ (corner i (star x*x)) = τ (corner i (x*star x)) := by
  simpa using τ.square_swap (corner i x)

theorem corner_square_equal (τ : OneQuasitrace (CStarMatrix n n A)) (i j : n) (x : A) :
    τ (corner i (star x*x)) = τ (corner j (star x*x)) := by
  have h := τ.square_swap (entry i j x)
  simp only [entry_star, entry_mul] at h
  exact (corner_square_swap τ i x).trans h.symm

theorem map_diagonal (τ : OneQuasitrace (CStarMatrix n n A)) (a : n → A)
    (ha : ∀ i, IsSelfAdjoint (a i)) :
    τ (diagonal a) = ∑ i, τ (corner i (a i)) := by
  rw [diagonal_eq_sum]
  apply τ.map_sum
  · intro i _; exact corner_selfAdjoint i (ha i)
  · intro i _ j _
    by_cases hij : i = j
    · subst j; exact Commute.refl _
    · exact corner_commute hij _ _

end Kaplansky

end
end

end OAI
