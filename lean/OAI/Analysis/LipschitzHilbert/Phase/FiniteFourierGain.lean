import OAI.Analysis.LipschitzHilbert.Estimates.BoundedDuality
import OAI.Analysis.LipschitzHilbert.Fourier.SimpleFourierPairing
import OAI.Analysis.LipschitzHilbert.Fourier.FourierHomogeneity

namespace OAI

/-! The scalar finite Fourier gain for every real exponent `p ≥ 4`. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

theorem normalized_finite_fourier_power_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap D p : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) (hp : 4 ≤ p)
    (ha : (∑ i, ‖a i‖ ^ fourierInterpolationExponent D p) = 1) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ p ∂ν) ≤ 1 := by
  apply bounded_lp_power_le_one_of_simple_tests ν (finiteFourierSum frequency a)
    (continuous_finiteFourierSum frequency a).measurable
    (Finset.sum_nonneg (fun i _ => norm_nonneg (a i))) (finiteFourierSum_bound frequency a)
    (by linarith)
  intro g
  exact simpleFunc_fourier_pairing_bound_at_p ν frequency hgap hsep hν hD hcard hp a g ha

theorem finite_fourier_power_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap D p : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) (hp : 4 ≤ p) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ p ∂ν) ≤
      sequenceNorm a (fourierInterpolationExponent D p) ^ p := by
  have hr := (fourier_interpolation_parameters hD hp).1
  apply homogeneous_fourier_power_bound ν frequency hr (by linarith) _ a
  intro b hb
  exact normalized_finite_fourier_power_gain ν frequency b hgap hsep hν hD hcard hp hb

/-- The scalar form of Proposition `phase:finite-fourier`, with its exact
constant one and its logarithmic improvement in the coefficient exponent. -/
theorem finite_fourier_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap D p : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) (hp : 4 ≤ p) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ p ∂ν) ^ (1 / p) ≤
      sequenceNorm a (fourierInterpolationExponent D p) := by
  have hp0 : 0 < p := by linarith
  have h := Real.rpow_le_rpow
    (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))
    (finite_fourier_power_gain ν frequency a hgap hsep hν hD hcard hp)
    (show 0 ≤ 1 / p by positivity)
  rw [← Real.rpow_mul (sequenceNorm_nonneg a _)] at h
  have heq : p * (1 / p) = 1 := by field_simp
  simpa only [heq, Real.rpow_one] using h

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
