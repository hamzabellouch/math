import OAI.Analysis.KadisonKastler.PreservationMatrix
import Mathlib.Data.Fintype.Perm

namespace OAI

/-! # Passing between ordered tuples and their underlying subsets -/

namespace KadisonKastler

open Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I J R S : Type*} [Fintype I] [Fintype J] [Fintype R] [Fintype S]
  [DecidableEq R] [DecidableEq S]

local instance tupleMatrixOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance tupleMatrixStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

def fiberReplication (f : I → R) : CStarMatrix I R (H →L[ℂ] H) :=
  CStarMatrix.ofMatrix fun i r => if f i = r then 1 else 0

theorem norm_fiberReplication_le (f : I → R) (m : ℕ)
    (hf : ∀ r, #{i | f i = r} ≤ m) :
    ‖fiberReplication (H := H) f‖ ≤ Real.sqrt (m : ℝ) := by
  classical
  have h := norm_matrix_le_sqrt_degrees (fiberReplication (H := H) f)
    (fun i r => f i = r) 1 m
  simp only [Nat.cast_one, one_mul] at h
  apply h
  · intro i r hir
    change (if f i = r then (1 : H →L[ℂ] H) else 0) = 0
    simp [hir]
  · intro i r
    change ‖if f i = r then (1 : H →L[ℂ] H) else 0‖ ≤ 1
    split_ifs
    · exact ContinuousLinearMap.norm_id_le
    · simp
  · intro i
    apply card_le_one.mpr
    intro x hx y hy
    simp only [mem_filter, mem_univ, true_and] at hx hy
    exact hx.symm.trans hy
  · exact hf

omit [CompleteSpace H] [Fintype I] [Fintype S] [DecidableEq S] in
theorem fiberReplication_mul (f : I → R) (T : CStarMatrix R S (H →L[ℂ] H))
    (i : I) (s : S) : (fiberReplication (H := H) f * T) i s = T (f i) s := by
  change (∑ j, (if f i = j then (1 : H →L[ℂ] H) else 0) * T j s) = T (f i) s
  simp [ite_mul, eq_comm]

omit [Fintype I] [Fintype J] in
theorem mul_fiberReplication_star (g : J → S) (T : CStarMatrix I S (H →L[ℂ] H))
    (i : I) (j : J) : (T * (fiberReplication (H := H) g).conjTranspose) i j = T i (g j) := by
  change (∑ s, T i s * star (if g j = s then (1 : H →L[ℂ] H) else 0)) = T i (g j)
  simp only [apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero]
  simp [eq_comm]

/-- Replication of each row and column costs only the square roots of
the numbers of orderings, rather than their product. -/
theorem norm_replicatedMatrix_le (f : I → R) (g : J → S)
    (m n : ℕ) (hf : ∀ r, #{i | f i = r} ≤ m) (hg : ∀ s, #{j | g j = s} ≤ n)
    (T : CStarMatrix R S (H →L[ℂ] H)) :
    ‖CStarMatrix.ofMatrix (fun i j => T (f i) (g j))‖ ≤
      Real.sqrt (m : ℝ) * ‖T‖ * Real.sqrt (n : ℝ) := by
  have he : CStarMatrix.ofMatrix (fun i j => T (f i) (g j)) =
      fiberReplication (H := H) f * T * (fiberReplication (H := H) g).conjTranspose := by
    apply CStarMatrix.ext
    intro i j
    rw [mul_fiberReplication_star, fiberReplication_mul]
    rfl
  rw [he]
  apply (rectangularOperator_norm_mul_le _ _).trans
  apply mul_le_mul
  · exact (rectangularOperator_norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fiberReplication_le f m hf) (norm_nonneg _))
  · rw [norm_rectangular_star]
    exact norm_fiberReplication_le g n hg
  · positivity
  · positivity

end

end KadisonKastler

end OAI
