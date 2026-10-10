import Mathlib

namespace OAI

/-! Matrix Compact Bounds. -/

noncomputable section
open Matrix Set
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
namespace MongeAmpere
variable {n : Type*} [Fintype n]
local notation "Mat" => Matrix n n ℂ

lemma compact_matrix_bound {f : Mat → ℝ} (hf : Continuous f) (B : ℝ) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ H : Mat, ‖H‖ ≤ B → f H ≤ Q := by
  obtain ⟨b,hb⟩ := (isCompact_closedBall (0:Mat) B).bddAbove_image hf.continuousOn
  refine ⟨max b 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun H hH => ?_⟩
  exact (hb (mem_image_of_mem _ (by simpa only [Metric.mem_closedBall,dist_zero_right] using hH))).trans
    (le_max_left _ _)

lemma matrix_norm_le_of_entries {H : Mat} {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ i j, ‖H i j‖ ≤ B) : ‖H‖ ≤ B := by
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  exact (pi_norm_le_iff_of_nonneg hB).mpr (hH i)

variable [DecidableEq n]

lemma posDef_eq_det_smul_adjugate_inv (H : Mat) (hH : H.PosDef) :
    H = H.det • H⁻¹.adjugate := by
  let : Invertible H := Matrix.invertibleOfIsUnitDet H (isUnit_iff_ne_zero.mpr hH.det_pos.ne')
  calc
    H = H⁻¹⁻¹ := (Matrix.inv_inv_of_invertible H).symm
    _ = (Ring.inverse H⁻¹.det) • H⁻¹.adjugate := Matrix.inv_def _
    _ = H.det • H⁻¹.adjugate := by rw [Matrix.det_nonsing_inv]; simp only [Ring.inverse_eq_inv',inv_inv]

lemma posDef_norm_det (H : Mat) (hH : H.PosDef) : ‖H.det‖ = H.det.re := by
  have he : H.det = (H.det.re:ℂ) := Complex.ext rfl (by simpa using (Complex.pos_iff.mp hH.det_pos).2.symm)
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Complex.pos_iff.mp hH.det_pos).1.le]
  rfl

lemma metric_norm_bound_from_inverse (B : ℝ) : ∃ Q : ℝ, 0 < Q ∧
    ∀ H : Mat, H.PosDef → ‖H⁻¹‖ ≤ B → ‖H‖ ≤ H.det.re*Q := by
  obtain ⟨Q,hQ,hb⟩ := compact_matrix_bound (show Continuous (fun H : Mat => ‖H.adjugate‖) from
    (continuous_id.matrix_adjugate : Continuous (fun H : Mat => H.adjugate)).norm) B
  refine ⟨Q,hQ,fun H hH hi => ?_⟩
  calc
    ‖H‖ = ‖H.det • H⁻¹.adjugate‖ := congrArg norm (posDef_eq_det_smul_adjugate_inv H hH)
    _ = H.det.re*‖H⁻¹.adjugate‖ := by rw [norm_smul,posDef_norm_det H hH]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb _ hi) (Complex.pos_iff.mp hH.det_pos).1.le

end MongeAmpere

end

end OAI
