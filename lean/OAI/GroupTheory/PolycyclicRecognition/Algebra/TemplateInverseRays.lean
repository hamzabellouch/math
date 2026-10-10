import OAI.GroupTheory.PolycyclicRecognition.Geometry.TemplateWeightRays

namespace OAI

/-! # Locating each source generator in the pulled-back target rays -/

noncomputable section
namespace PolycyclicRecognition

variable {W I B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

/-- Apply the ray theorem to the inverse symmetry. This identifies the
target ray whose pullback contains any specified source generator. -/
theorem templateSymmetry_inverse_weight_ray
    (D : SupportDatum W I B) (A : templateSymmetryGroup D)
    (j : I) (hj : D.weight j ≠ 0) :
    ∃ (i : I) (c : ℝ), 0 < c ∧ (D.weight i).comp A.val.toLinearMap = c • D.weight j := by
  obtain ⟨i, r, hr, he⟩ := templateSymmetry_weight_ray D A⁻¹ j hj
  refine ⟨i, r⁻¹, inv_pos.mpr hr, ?_⟩
  ext w
  have h := LinearMap.congr_fun he (A.val w)
  change D.weight j ((A⁻¹).val (A.val w)) = r * D.weight i (A.val w) at h
  have hi : (A⁻¹).val (A.val w) = w := A.val.symm_apply_apply w
  rw [hi] at h
  change D.weight i (A.val w) = r⁻¹ * D.weight j w
  rw [h, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

end PolycyclicRecognition

end

end OAI
