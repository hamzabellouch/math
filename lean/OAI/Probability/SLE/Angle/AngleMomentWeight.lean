import OAI.Probability.SLE.Angle.TargetAngleLaw
import OAI.Probability.SLE.BoundaryDensity

namespace OAI

/-! The angular singularity in the centered moment estimate is
integrable against the exact invariant angle law. -/

noncomputable section
open Set Filter MeasureTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Target

lemma angle_inverse_sine_lintegral_lt_top (κ : ℝ) :
    (∫⁻ θ, ENNReal.ofReal (1/(Real.sin θ)^greenExponent κ) ∂angleLaw κ)<∞ := by
  let μ := volume.restrict (Ioo (0:ℝ) Real.pi)
  let w := fun θ => ENNReal.ofReal ((Real.sin θ)^(4*a κ))
  have hm : Measurable w := (measurable_id.sin.pow_const (4*a κ)).ennreal_ofReal
  have hf : Measurable (fun θ : ℝ => ENNReal.ofReal (1/(Real.sin θ)^greenExponent κ)) :=
    (measurable_const.div (measurable_id.sin.pow_const (greenExponent κ))).ennreal_ofReal
  change (∫⁻ θ, ENNReal.ofReal (1/(Real.sin θ)^greenExponent κ)
    ∂((μ.withDensity w) univ)⁻¹ • μ.withDensity w)<∞
  rw [lintegral_smul_measure,lintegral_withDensity_eq_lintegral_mul μ hm hf]
  apply ENNReal.mul_lt_top
  · exact ENNReal.inv_lt_top.mpr (angle_normalizer_pos κ)
  · apply lt_of_le_of_lt (lintegral_mono_ae ?_) (show (∫⁻ _ : ℝ, (1:ℝ≥0∞) ∂μ)<∞ from by
      simp only [μ,lintegral_const,one_mul,Measure.restrict_apply_univ,Real.volume_Ioo,sub_zero]
      exact ENNReal.ofReal_lt_top)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hs : 0<Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    change ENNReal.ofReal ((Real.sin θ)^(4*a κ))*
      ENNReal.ofReal (1/(Real.sin θ)^greenExponent κ)≤1
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),mul_one_div,
      ← Real.rpow_sub hs]
    have he : 4*a κ-greenExponent κ=1 := by unfold a greenExponent; ring
    rw [he,Real.rpow_one]
    exact (ENNReal.ofReal_le_ofReal (Real.sin_le_one θ)).trans_eq (by norm_num)

lemma angle_inverse_sine_integrable (κ : ℝ) :
    Integrable (fun θ => 1/(Real.sin θ)^greenExponent κ) (angleLaw κ) := by
  refine ⟨(measurable_const.div (measurable_id.sin.pow_const (greenExponent κ))).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal ?_).mpr (angle_inverse_sine_lintegral_lt_top κ)
  filter_upwards [angleLaw_ae_mem κ] with θ hθ
  exact one_div_nonneg.mpr (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le _)

end SLEExactGauge.Target

end

end OAI
