import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem weightedGram_eq_sum (A : Matrix κ κ ℝ) (w : κ → ℝ) :
    A * Matrix.diagonal w * A.transpose =
      ∑ k, w k • Matrix.vecMulVec (fun i => A i k) (fun i => A i k) := by
  funext i j
  rw [Matrix.mul_apply, Matrix.sum_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem weightedGram_isUnit (A : Matrix κ κ ℝ) (w : κ → ℝ)
    (hA : IsUnit A) (hw : ∀ k, w k ≠ 0) : IsUnit (A * Matrix.diagonal w * A.transpose) := by
  have hD : IsUnit (Matrix.diagonal w) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => hw k)
  exact (hA.mul hD).mul ((Matrix.isUnit_transpose A).mpr hA)

end Zarankiewicz

end

end OAI
