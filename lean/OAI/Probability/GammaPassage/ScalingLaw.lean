import OAI.Probability.GammaPassage.TiltDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

/-- Scalar change of variables for a measurable nonnegative density. -/
lemma map_mul_withDensity_real {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measure.map (fun x : ℝ => a * x) (volume.withDensity f) =
      volume.withDensity (fun y => ENNReal.ofReal a⁻¹ * f (y / a)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul volume hf
      (g := fun x : ℝ => g (a * x)) (hg.comp (by fun_prop)),
    lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) hg]
  have hchange :
      (∫⁻ y : ℝ, f (y / a) * g y ∂Measure.map (fun x : ℝ => a * x) volume) =
        ∫⁻ x : ℝ, f x * g (a * x) := by
    rw [lintegral_map (by fun_prop) (by fun_prop)]
    simp only [mul_div_cancel_left₀ _ ha.ne']
  rw [Real.map_volume_mul_left ha.ne', abs_of_pos (inv_pos.mpr ha),
    lintegral_smul_measure, smul_eq_mul] at hchange
  calc
    (∫⁻ x : ℝ, (f * fun x => g (a * x)) x) =
        ENNReal.ofReal a⁻¹ * ∫⁻ y : ℝ, f (y / a) * g y := hchange.symm
    _ = ∫⁻ y : ℝ, (fun y => ENNReal.ofReal a⁻¹ * f (y / a)) y * g y := by
      rw [← lintegral_const_mul _ (by fun_prop)]
      apply lintegral_congr
      intro y
      exact (mul_assoc _ _ _).symm

/-- The Gamma density satisfies the scaling Jacobian identity, including at the origin. -/
lemma gammaPDF_scaling {shape rate a : ℝ} (hshape : 0 < shape) (hrate : 0 < rate)
    (ha : 0 < a) (y : ℝ) :
    ENNReal.ofReal a⁻¹ * gammaPDF shape rate (y / a) =
      gammaPDF shape (rate / a) y := by
  by_cases hy : 0 ≤ y
  · rw [gammaPDF_of_nonneg (div_nonneg hy ha.le), gammaPDF_of_nonneg hy,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)]
    congr 1
    rw [Real.div_rpow hy ha.le, Real.div_rpow hrate.le ha.le,
      Real.rpow_sub ha shape 1, Real.rpow_one]
    have he : -(rate * (y / a)) = -((rate / a) * y) := by ring
    rw [he]
    field_simp [ha.ne', (Real.rpow_pos_of_pos ha shape).ne',
      (Real.Gamma_pos_of_pos hshape).ne']
  · rw [gammaPDF_of_neg (div_neg_of_neg_of_pos (lt_of_not_ge hy) ha),
      gammaPDF_of_neg (lt_of_not_ge hy), mul_zero]

/-- Scaling a Gamma random variable by a positive constant divides its rate. -/
theorem map_mul_gammaMeasure {shape rate a : ℝ} (hshape : 0 < shape)
    (hrate : 0 < rate) (ha : 0 < a) :
    Measure.map (fun x : ℝ => a * x) (gammaMeasure shape rate) =
      gammaMeasure shape (rate / a) := by
  change Measure.map _ (volume.withDensity (gammaPDF shape rate)) =
    volume.withDensity (gammaPDF shape (rate / a))
  rw [map_mul_withDensity_real ha (by unfold gammaPDF; fun_prop)]
  congr 1
  funext y
  exact gammaPDF_scaling hshape hrate ha y

/-- The scaling pushforward equals the measure weighted by the Gamma likelihood. -/
theorem map_mul_gammaMeasure_eq_tilt {shape rate a : ℝ} (hshape : 0 < shape)
    (hrate : 0 < rate) (ha : 0 < a) :
    Measure.map (fun x : ℝ => a * x) (gammaMeasure shape rate) =
      (gammaMeasure shape rate).withDensity
        (fun x => ENNReal.ofReal (gammaScaleLikelihood shape rate a x)) := by
  rw [map_mul_gammaMeasure hshape hrate ha,
    gammaMeasure_withDensity_scaleLikelihood hshape hrate ha]
end GammaFPP

end OAI
