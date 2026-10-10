import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportTemplates

namespace OAI

/-! # Prescribed endpoint times realizing the segment support exponents -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [Fintype I] [Fintype B] (D : SupportDatum W I B)

theorem weightSupport_segment_endpoints (w₀ w₁ : W) (i : I) :
    D.weightSupport (segment ℝ w₀ w₁) i = max (D.weight i w₀) (D.weight i w₁) := by
  unfold weightSupport
  change sSup ((D.weight i).toAffineMap '' segment ℝ w₀ w₁) = _
  rw [image_segment]
  simp only [LinearMap.coe_toAffineMap]
  rw [segment_eq_Icc']
  exact csSup_Icc min_le_max

/-- A linear weight on the segment chooses the final time exactly when its
value on the direction is nonnegative. -/
def segmentSupportTime (v : W) (T : ℝ) (i : I) : ℝ :=
  if 0 ≤ D.weight i v then T else 0

theorem segmentSupportTime_mem (v : W) {T : ℝ} (hT : 0 ≤ T) (i : I) :
    D.segmentSupportTime v T i ∈ Icc 0 T := by
  by_cases hi : 0 ≤ D.weight i v <;> simp [segmentSupportTime, hi, hT]

/-- These fixed times give precisely the exponents used by the normalized
segment boxes, rather than arbitrary height support positions. -/
theorem weight_at_segmentSupportTime (w₀ v : W) {T : ℝ} (hT : 0 ≤ T) (i : I) :
    D.weight i (w₀ + D.segmentSupportTime v T i • v) =
      D.weightSupport (segment ℝ w₀ (w₀ + T • v)) i := by
  rw [weightSupport_segment_endpoints]
  by_cases hi : 0 ≤ D.weight i v
  · simp only [segmentSupportTime, ite_eq_left hi, map_add, map_smul, smul_eq_mul]
    exact (max_eq_right (by nlinarith [mul_nonneg hT hi])).symm
  · simp only [segmentSupportTime, ite_eq_right hi, zero_smul, add_zero, map_add, map_smul, smul_eq_mul]
    exact (max_eq_left (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hT (le_of_not_ge hi)])).symm

end PolycyclicRecognition.SupportDatum

end

end OAI
