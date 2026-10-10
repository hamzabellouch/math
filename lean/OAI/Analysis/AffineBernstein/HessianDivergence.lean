import Mathlib
import OAI.Analysis.AffineBernstein.Basic
import OAI.Analysis.AffineBernstein.PiolaDifferential

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- Smoothness through order three suffices for the cofactor cancellation. -/
theorem adjugate_hessian_divergence {n : ℕ} (u : Space n → ℝ) (x : Space n)
    (hu : ContDiffAt ℝ 3 u x) (i : Fin n) :
    (∑ j, fderiv ℝ (fun y => (hessian u y).adjugate i j) x
      (coordinateVector n j)) = 0 := by
  let F : Fin n → Space n → ℝ := fun l y => fderiv ℝ u y (coordinateVector n l)
  have hF (l : Fin n) : ContDiffAt ℝ 2 (F l) x :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  have hJ (y : Space n) : jacobianRows F (coordinateVector n) y =
      (hessian u y).transpose := rfl
  simpa only [hJ, ← Matrix.adjugate_transpose, Matrix.transpose_apply] using
    piola_identity F (coordinateVector n) x hF i

/-- For an invertible Hessian, the manuscript's definition is exactly the adjugate. -/
theorem cofactorHessian_eq_adjugate {n : ℕ} (u : Space n → ℝ) (x : Space n)
    (hdet : (hessian u x).det ≠ 0) : cofactorHessian u x = (hessian u x).adjugate := by
  unfold cofactorHessian
  rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hdet, one_smul]

/-- The Hessian cofactor is symmetric under the standing positivity hypothesis. -/
theorem cofactorHessian_isSymm {n : ℕ} (u : Space n → ℝ) (x : Space n)
    (hpos : (hessian u x).PosDef) : (cofactorHessian u x).IsSymm := by
  rw [cofactorHessian_eq_adjugate u x (ne_of_gt hpos.det_pos)]
  exact (Matrix.isHermitian_iff_isSymm.mp hpos.isHermitian).adjugate

/-- Both divergences of the actual coefficient matrix vanish on the original domain. -/
theorem cofactorHessian_divergence {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    (u : Space n → ℝ) (hu : ContDiffOn ℝ 3 u Ω)
    (hpos : ∀ x ∈ Ω, (hessian u x).PosDef) (x : Space n) (hx : x ∈ Ω) (i : Fin n) :
    (∑ j, fderiv ℝ (fun y => cofactorHessian u y i j) x (coordinateVector n j)) = 0 ∧
    (∑ j, fderiv ℝ (fun y => cofactorHessian u y j i) x (coordinateVector n j)) = 0 := by
  have hrow : (∑ j, fderiv ℝ (fun y => cofactorHessian u y i j) x
      (coordinateVector n j)) = 0 := by
    have he (j : Fin n) : (fun y => cofactorHessian u y i j) =ᶠ[nhds x]
        (fun y => (hessian u y).adjugate i j) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      rw [cofactorHessian_eq_adjugate u y (ne_of_gt (hpos y hy).det_pos)]
    simp_rw [(he _).fderiv_eq]
    exact adjugate_hessian_divergence u x (hu.contDiffAt (hΩ.mem_nhds hx)) i
  refine ⟨hrow, ?_⟩
  have he (j : Fin n) : (fun y => cofactorHessian u y j i) =ᶠ[nhds x]
      (fun y => cofactorHessian u y i j) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact (cofactorHessian_isSymm u y (hpos y hy)).apply i j
  simpa only [(he _).fderiv_eq] using hrow

end AffineBernstein
end

end OAI
