import OAI.Geometry.NodalSets.Elliptic.CorrugationNormalizedGradient

namespace OAI

namespace Yau.Geometry
open Filter
open scoped Topology
noncomputable section

lemma corrugationGradientRate_factor {L : ℝ} (hL : L ≠ 0) (k : ℕ) :
    corrugationGradientRate L k = corrugationScale L k*
      (1+(L^2)⁻¹/((k:ℝ)+1)^4) := by
  rw [corrugationGradientRate,corrugationScale_formula,corrugationFrequency]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma corrugationGradientRate_le_scale {L : ℝ} (hL : 0 < L) :
    ∀ᶠ k : ℕ in atTop, corrugationGradientRate L k ≤ 2*corrugationScale L k := by
  have ht := corrugation_power_reciprocal_tendsto ((L^2)⁻¹) (by norm_num : (4:ℕ) ≠ 0)
  filter_upwards [ht.eventually_lt_const zero_lt_one] with k hk
  rw [corrugationGradientRate_factor hL.ne' k]
  have hR := corrugationScale_positive hL k
  nlinarith

lemma corrugation_low_tilt_le_scale {L T : ℝ} (hL : 0 < L) :
    ∀ᶠ k : ℕ in atTop, ∀ (χ l : ℝ),
      corrugationFrequency k*χ*l ≤ T → χ*l ≤ corrugationScale L k := by
  have ht : Tendsto (fun k ↦ T/(corrugationFrequency k*corrugationScale L k)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using
      (corrugation_frequency_scale_tendsto hL).inv_tendsto_atTop.const_mul T
  filter_upwards [ht.eventually_lt_const zero_lt_one] with k hk
  intro χ l hreg
  have hJ := corrugationFrequency_positive k
  have hR := corrugationScale_positive hL k
  have hTR : T ≤ corrugationFrequency k*corrugationScale L k :=
    (div_le_one (mul_pos hJ hR)).mp hk.le
  exact (mul_le_mul_iff_right₀ hJ).mp (by nlinarith : corrugationFrequency k*(χ*l) ≤ corrugationFrequency k*corrugationScale L k)

end
end Yau.Geometry

end OAI
