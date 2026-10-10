import OAI.Probability.SLE.MomentGauge

namespace OAI

/-! The angle law in the prescribed coefficient formula is a probability
measure supported on the nondegenerate disk charts. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal

namespace SLEExactGauge.Target

lemma angleLaw_ae_mem (κ : ℝ) : ∀ᵐ θ ∂angleLaw κ, θ ∈ Ioo (0:ℝ) Real.pi := by
  have h : ∀ᵐ θ ∂(volume.restrict (Ioo (0:ℝ) Real.pi)).withDensity
      (fun θ => ENNReal.ofReal (Real.sin θ ^ (4*a κ))), θ ∈ Ioo (0:ℝ) Real.pi :=
    (ae_restrict_mem measurableSet_Ioo).filter_mono
      (withDensity_absolutelyContinuous _ _).ae_le
  exact Measure.ae_smul_measure h _

lemma angle_normalizer_pos (κ : ℝ) :
    0 < ((volume.restrict (Ioo (0:ℝ) Real.pi)).withDensity
      (fun θ => ENNReal.ofReal (Real.sin θ ^ (4*a κ)))) univ := by
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have hm : Measurable (fun θ : ℝ => ENNReal.ofReal (Real.sin θ ^ (4*a κ))) :=
    (measurable_id.sin.pow_const (4*a κ)).ennreal_ofReal
  rw [setLIntegral_pos_iff hm]
  have he : Function.support (fun θ : ℝ => ENNReal.ofReal (Real.sin θ ^ (4*a κ))) ∩
      Ioo (0:ℝ) Real.pi = Ioo (0:ℝ) Real.pi := by
    apply inter_eq_right.mpr
    intro θ hθ
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) _)).ne'
  rw [he,Real.volume_Ioo,sub_zero]
  exact ENNReal.ofReal_pos.mpr Real.pi_pos

lemma angle_normalizer_lt_top {κ : ℝ} (hκ : 0 < κ) :
    ((volume.restrict (Ioo (0:ℝ) Real.pi)).withDensity
      (fun θ => ENNReal.ofReal (Real.sin θ ^ (4*a κ)))) univ < ∞ := by
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have hpow : 0 ≤ 4*a κ := mul_nonneg (by norm_num) (div_nonneg (by norm_num) hκ.le)
  have hle : (∫⁻ θ in Ioo (0:ℝ) Real.pi,
      ENNReal.ofReal (Real.sin θ ^ (4*a κ))) ≤
      ∫⁻ _ in Ioo (0:ℝ) Real.pi, (1:ℝ≥0∞) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_one (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le
        (Real.sin_le_one θ) hpow)).trans_eq (by norm_num)
  exact hle.trans_lt (by simp only [lintegral_const,one_mul,
    Measure.restrict_apply_univ,Real.volume_Ioo,sub_zero]; exact ENNReal.ofReal_lt_top)

theorem angleLaw_isProbability {κ : ℝ} (hκ : 0 < κ) : IsProbabilityMeasure (angleLaw κ) := by
  constructor
  change _⁻¹ * _ = (1:ℝ≥0∞)
  exact ENNReal.inv_mul_cancel (angle_normalizer_pos κ).ne'
    (angle_normalizer_lt_top hκ).ne

end SLEExactGauge.Target

end

end OAI
