import OAI.Probability.FreeIsing.Gaussian.IntegrationByParts
import OAI.Probability.FreeIsing.Posterior.SqrtObservationDerivative

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace Problem367

def gaussianObservationMean (f : ℝ → ℝ) (signal t : ℝ) : ℝ :=
  ∫ z, f (t * signal + Real.sqrt t * z) ∂gaussianReal 0 1

theorem hasDerivAt_gaussianObservationMean_raw
    {f f' : ℝ → ℝ} {C D : ℝ} (signal : ℝ) {t : ℝ} (ht : 0 < t)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hbound : ∀ x, |f x| ≤ C) (hbound' : ∀ x, |f' x| ≤ D) :
    HasDerivAt (gaussianObservationMean f signal)
      (∫ z, f' (t * signal + Real.sqrt t * z) *
        (signal + z / (2 * Real.sqrt t)) ∂gaussianReal 0 1) t := by
  have hfm' : Measurable f' := by
    have heq : f' = deriv f := funext (fun x => (hf x).deriv.symm)
    rw [heq]
    exact measurable_deriv f
  exact (hasDerivAt_integral_sqrt_observation (integrable_const signal)
    ((memLp_id_gaussianReal 1).integrable (by norm_num)) hf hfm' hbound
    ((abs_nonneg (f' 0)).trans (hbound' 0)) hbound' ht).2

theorem hasDerivAt_gaussianObservationMean
    {f f' f'' : ℝ → ℝ} {C D E : ℝ} (signal : ℝ) {t : ℝ} (ht : 0 < t)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x, |f x| ≤ C) (hbound' : ∀ x, |f' x| ≤ D)
    (hbound'' : ∀ x, |f'' x| ≤ E) :
    HasDerivAt (gaussianObservationMean f signal)
      (signal * (∫ z, f' (t * signal + Real.sqrt t * z) ∂gaussianReal 0 1) +
        (1 / 2 : ℝ) * ∫ z, f'' (t * signal + Real.sqrt t * z) ∂gaussianReal 0 1) t := by
  have hraw := hasDerivAt_gaussianObservationMean_raw signal ht hf hbound hbound'
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr (fun x => (hf' x).continuousAt)
  have hfm : Measurable (fun z => f' (t * signal + Real.sqrt t * z)) :=
    hf'c.measurable.comp (by fun_prop)
  have hb : ∀ᵐ z ∂gaussianReal 0 1,
      ‖f' (t * signal + Real.sqrt t * z)‖ ≤ D :=
    Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hbound' _)
  have hi : Integrable (fun z => f' (t * signal + Real.sqrt t * z)) (gaussianReal 0 1) :=
    Integrable.of_bound hfm.aestronglyMeasurable D hb
  have hzi : Integrable (fun z => z * f' (t * signal + Real.sqrt t * z))
      (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal 1).integrable (by norm_num)).mul_bdd hfm.aestronglyMeasurable hb
  have hibp := gaussian_integral_mul_affine_of_bounded_deriv
    (t * signal) (Real.sqrt t) hf' hbound' hbound''
  have hsplit :
      (fun z => f' (t * signal + Real.sqrt t * z) * (signal + z / (2 * Real.sqrt t))) =
      (fun z => signal * f' (t * signal + Real.sqrt t * z) +
        (1 / (2 * Real.sqrt t)) * (z * f' (t * signal + Real.sqrt t * z))) := by
    funext z
    ring
  rw [hsplit, integral_add (hi.const_mul signal) (hzi.const_mul _),
    integral_const_mul, integral_const_mul, hibp] at hraw
  convert hraw using 1
  have hroot : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  field_simp

end Problem367

end

end OAI
