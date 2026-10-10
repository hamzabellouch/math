import OAI.Probability.InvariantIsing.Gaussian.MPDensityIntegrability

namespace OAI

/-! Normalization of the literal density and atom appearing in the MP application input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

lemma marchenkoPasturMeasure_eq_density (α : ℝ) :
    marchenkoPasturMeasure α = ENNReal.ofReal (max (1-α) 0) • Measure.dirac 0+
      (volume.restrict (Icc (marchenkoPasturA α) (marchenkoPasturB α))).withDensity
        (fun x => ENNReal.ofReal (mpDensity α x)) := by
  unfold marchenkoPasturMeasure
  rw [withDensity_indicator measurableSet_Icc]
  rfl

theorem marchenkoPastur_probability {α : ℝ} (hα : 0 < α) :
    IsProbabilityMeasure (marchenkoPasturMeasure α) := by
  constructor
  rw [marchenkoPasturMeasure_eq_density,Measure.add_apply,Measure.smul_apply,
    measure_univ,smul_eq_mul,mul_one,withDensity_apply _ MeasurableSet.univ]
  simp only [setLIntegral_univ]
  have hn : 0 ≤ᵐ[volume.restrict (Icc (marchenkoPasturA α) (marchenkoPasturB α))] mpDensity α :=
    (ae_restrict_mem measurableSet_Icc).mono (fun _ hx => mpDensity_nonneg hx)
  rw [← ofReal_integral_eq_lintegral_ofReal (mpDensity_integrable hα) hn,
    mpDensity_integral hα,
    ← ENNReal.ofReal_add (le_max_right (1-α) 0) (le_min (by norm_num) hα.le),
    mp_total_mass,ENNReal.ofReal_one]

end InvariantIsing

end

end OAI
