import OAI.Probability.InvariantIsing.Gaussian.MPDensityProbability
import OAI.Probability.InvariantIsing.Gaussian.GaussianGramEmpiricalTransform

namespace OAI

/-! The positive resolvent transform of the literal Marchenko--Pastur measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
namespace InvariantIsing

lemma mpDensity_measure_integral (α : ℝ) (g : ℝ → ℝ) :
    (∫ x, g x ∂(volume.restrict (Icc (marchenkoPasturA α) (marchenkoPasturB α))).withDensity
      (fun x => ENNReal.ofReal (mpDensity α x))) =
    ∫ x in Icc (marchenkoPasturA α) (marchenkoPasturB α), mpDensity α x*g x := by
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_mpDensity α).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [ENNReal.toReal_ofReal (mpDensity_nonneg hx),smul_eq_mul]

theorem marchenkoPastur_transform {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    (∫ x, positiveResolventTest t x ∂marchenkoPasturMeasure α) =
      marchenkoPasturTransform t α := by
  have := marchenkoPastur_probability hα
  let ν := (volume.restrict (Icc (marchenkoPasturA α) (marchenkoPasturB α))).withDensity
    (fun x => ENNReal.ofReal (mpDensity α x))
  have hν : ν ≤ marchenkoPasturMeasure α := by
    rw [marchenkoPasturMeasure_eq_density]
    exact Measure.le_add_left le_rfl
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le _ hν
  have : IsFiniteMeasure (ENNReal.ofReal (max (1-α) 0) • Measure.dirac (0 : ℝ)) :=
    (Measure.dirac (0 : ℝ)).smul_finite ENNReal.ofReal_ne_top
  have hi (μ : Measure ℝ) [IsFiniteMeasure μ] : Integrable (positiveResolventTest t) μ := by
    apply (integrable_const (1/t)).mono' (continuous_positiveResolventTest ht).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (positiveResolventTest_bound ht x).1]
      exact (positiveResolventTest_bound ht x).2
  have hv : (∫ x, positiveResolventTest t x ∂ν) =
      (2*α/Real.pi)*(∫ x in (0 : ℝ)..Real.pi,
        (sin x)^2/((1+α+2*sqrt α*cos x)*(t+(1+α+2*sqrt α*cos x)))) := by
    rw [mpDensity_measure_integral,mpDensity_substitution hα]
    have he : (∫ x in Icc 0 Real.pi,
        (2*α/Real.pi)*((sin x)^2/mpAngle α x)*positiveResolventTest t (mpAngle α x)) =
        ∫ x in Icc 0 Real.pi, (2*α/Real.pi)*
          ((sin x)^2/(mpAngle α x*(t+mpAngle α x))) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      unfold positiveResolventTest
      rw [max_eq_left (show 0 ≤ mpAngle α x from mp_angular_denominator_nonneg hα.le x)]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [he,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le pi_pos.le,
      intervalIntegral.integral_const_mul]
    rfl
  rw [marchenkoPasturMeasure_eq_density,integral_add_measure (hi _) (hi ν),
    integral_smul_measure,integral_dirac]
  change (ENNReal.ofReal (max (1-α) 0)).toReal*positiveResolventTest t 0+
    (∫ x, positiveResolventTest t x ∂ν) = _
  rw [ENNReal.toReal_ofReal (le_max_right _ _),hv]
  simpa only [positiveResolventTest,max_self,add_zero,mul_one_div] using mp_angular_transform hα ht

end InvariantIsing

end

end OAI
