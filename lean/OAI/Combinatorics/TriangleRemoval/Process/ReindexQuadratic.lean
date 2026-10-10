import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.StarInclusion

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave
open scoped Matrix.Norms.L2Operator

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
theorem reindex_quadratic (e : I ≃ J) (M : Matrix I I ℝ) (x : J → ℝ) :
    x ⬝ᵥ (Matrix.reindex e e M *ᵥ x) =
      (fun i => x (e i)) ⬝ᵥ (M *ᵥ fun i => x (e i)) := by
  simp only [dotProduct,Matrix.mulVec,Matrix.reindex_apply,Matrix.submatrix_apply]
  rw [← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply]

theorem hermitian_reindex_norm_le (e : I ≃ J) (M : Matrix I I ℝ) (hM : M.IsHermitian) :
    ‖Matrix.reindex e e M‖ ≤ ‖M‖ := by
  apply hermitian_norm_le_of_quadratic _ ((Matrix.isHermitian_reindex_iff e).mpr hM)
    ‖M‖ (norm_nonneg _)
  intro x
  rw [reindex_quadratic]
  have h := matrix_quadratic_abs M (fun i => x (e i))
  rw [show (∑ i, (x (e i))^2) = ∑ j, (x j)^2 from Equiv.sum_comp e (fun j => (x j)^2)] at h
  exact h

end SharpTerminalLeave

end
end

end OAI
