import OAI.Analysis.HenonEmden.Endpoints

namespace OAI

section LayerRecovery
open MeasureTheory Set Filter Topology
namespace HenonLaneEmden.WeightedLayers

lemma source_root {w u q : ℝ} (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) :
    (w*u^q)^(1/q) = w^(1/q)*u := by
  rw [Real.mul_rpow hw.le (Real.rpow_nonneg hu.le _), ← Real.rpow_mul hu.le]
  have h : q*(1/q) = 1 := by field_simp
  rw [h, Real.rpow_one]

lemma weighted_layer_identity {w u q : ℝ} (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) :
    (∫ t in 0..w*u^q, (u-(t/w)^(1/q))) = w*u^(q+1)/(q+1) := by
  have hq' : 0 < 1/q := one_div_pos.mpr hq
  have hf : 0 < w*u^q := mul_pos hw (Real.rpow_pos_of_pos hu _)
  have hr : IntervalIntegrable (fun t : ℝ => t^(1/q)) volume 0 (w*u^q) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have heq : (∫ t in 0..w*u^q, (u-(t/w)^(1/q))) =
      (∫ t in 0..w*u^q, (u-t^(1/q)/w^(1/q))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hf.le] at ht
    dsimp only
    rw [Real.div_rpow ht.1 hw.le]
  rw [heq, intervalIntegral.integral_sub (continuous_const.intervalIntegrable ..) (hr.div_const _),
    intervalIntegral.integral_const, intervalIntegral.integral_div,
    integral_rpow (Or.inl (by linarith : -1 < 1/q)),
    Real.zero_rpow (ne_of_gt (by linarith : 0 < 1/q+1)), sub_zero,
    sub_zero, smul_eq_mul]
  rw [Real.rpow_add hf, Real.rpow_one, source_root hw hu hq,
    Real.rpow_add hu, Real.rpow_one]
  have hw' : w^(1/q) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hw _)
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hq1 : q+1 ≠ 0 := by linarith
  field_simp [hw', hq0, hq1]
  ring

lemma layer_root_bounds {w u q t : ℝ} (hw : 0 < w) (hu : 0 < u) (hq : 0 < q)
    (ht : 0 ≤ t) (htf : t ≤ w*u^q) :
    0 ≤ (t/w)^(1/q) ∧ (t/w)^(1/q) ≤ u := by
  constructor
  · exact Real.rpow_nonneg (div_nonneg ht hw.le) _
  · have htw : t/w ≤ u^q := (div_le_iff₀ hw).mpr (by simpa [mul_comm] using htf)
    have hroot := Real.rpow_le_rpow (div_nonneg ht hw.le) htw (one_div_nonneg.mpr hq.le)
    rw [← Real.rpow_mul hu.le] at hroot
    have h : q*(1/q) = 1 := by field_simp
    rwa [h, Real.rpow_one] at hroot

/-- The exact scalar recovery inequality before integration. -/
lemma pressure_recovery_pointwise {h χ u τ endpoint error : ℝ}
    (hχ : 0 ≤ χ) (hχh : χ ≤ h) (hτ : 0 ≤ τ)
    (hend : |endpoint-τ| ≤ error*u) :
    h*(u-τ)-χ*(u-endpoint) ≤ (h-χ)*u+error*h*u := by
  have hhu : 0 ≤ error*u := le_trans (abs_nonneg _) hend
  have he := (abs_le.mp hend).2
  have hmul := mul_le_mul_of_nonneg_left he hχ
  have hmul' := mul_le_mul_of_nonneg_right hχh hhu
  have htail := mul_nonneg (sub_nonneg.mpr hχh) hτ
  nlinarith

end HenonLaneEmden.WeightedLayers
end LayerRecovery

end OAI
