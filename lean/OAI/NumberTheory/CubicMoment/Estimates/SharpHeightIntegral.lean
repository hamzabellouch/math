import OAI.NumberTheory.CubicMoment.Estimates.PrimeSharpCutoff
import OAI.NumberTheory.CubicMoment.Estimates.IntervalTransform
import OAI.NumberTheory.CubicMoment.Estimates.HeightPolynomialIntegral

namespace OAI

/-! The concrete sharp-cutoff smoothing in the manuscript's height variable.
The Fourier convention contributes the explicit Jacobian `1 / (2π)`.
All finite sums below retain their original coefficients and support. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
namespace CubicFirstMoment

def cutoffHeightMultiplier (T t : ℝ) : ℂ :=
  frequencyCutoff ((t/(2*Real.pi))/T) *
    𝓕 (fun x => (intervalStep 0 (Real.log 2) x : ℂ)) (t/(2*Real.pi))

lemma cutoffHeightMultiplier_integrable {T : ℝ} (hT : 0 < T) :
    Integrable (cutoffHeightMultiplier T) := by
  have h := (integrable_fourier_intervalSmoothing hT 0 (Real.log 2)).comp_div
    (show 2*Real.pi ≠ 0 by positivity)
  change Integrable (fun t => frequencyCutoff ((t/(2*Real.pi))/T) *
    𝓕 (fun x => (intervalStep 0 (Real.log 2) x : ℂ)) (t/(2*Real.pi)))
  simpa only [fourier_intervalSmoothing hT] using h

lemma cutoffHeightMultiplier_zero {T t : ℝ} (hT : 0 < T)
    (ht : 2*Real.pi*T ≤ |t|) : cutoffHeightMultiplier T t = 0 := by
  unfold cutoffHeightMultiplier
  rw [frequencyCutoff_zero, zero_mul]
  rw [abs_div, abs_div, abs_of_pos hT, abs_of_pos (by positivity : 0 < 2*Real.pi)]
  apply (le_div_iff₀ hT).mpr
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
  nlinarith

lemma smoothLogInterval_eq_height {T v : ℝ} (hT : 0 < T) :
    smoothLogInterval T v = ((2*Real.pi : ℝ) : ℂ)⁻¹ *
      heightFourierIntegral (cutoffHeightMultiplier T) (Real.log v) := by
  let f : ℝ → ℂ := fun ξ =>
    Complex.exp ((2*Real.pi*ξ*Real.log v : ℝ)*Complex.I) *
      (frequencyCutoff (ξ/T) *
        𝓕 (fun x => (intervalStep 0 (Real.log 2) x : ℂ)) ξ)
  calc
    smoothLogInterval T v = ∫ ξ : ℝ, f ξ :=
      concrete_interval_fourier_integral hT 0 (Real.log 2) (Real.log v)
    _ = ((2*Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, f (t/(2*Real.pi)) := by
      rw [Measure.integral_comp_div, abs_of_pos (by positivity : 0 < 2*Real.pi),
        Complex.real_smul, inv_mul_cancel_left₀ (by exact_mod_cast
          (show 2*Real.pi ≠ 0 by positivity))]
    _ = _ := by
      congr 1
      rw [heightFourierIntegral_eq]
      apply integral_congr_ae
      filter_upwards with t
      have he : 2*Real.pi*(t/(2*Real.pi))*Real.log v = Real.log v*t := by
        field_simp
      dsimp only [f, cutoffHeightMultiplier]
      rw [he, mul_comm]

/-- The smoothed finite arithmetic sum is the actual norm-twisted polynomial
integrated against the compact height multiplier. -/
theorem finite_smooth_interval_height (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {X T : ℝ} (hX : 0 < X) (hT : 0 < T)
    (hP : ∀ p ∈ P, p ≠ 0) :
    (∑ p ∈ P, c p*smoothLogInterval T (norm p/X)) =
      ((2*Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ,
        (cutoffHeightMultiplier T t * Complex.exp ((-Real.log X*t : ℝ)*Complex.I)) *
          ∑ p ∈ P, c p*normTwist t p := by
  calc
    _ = ((2*Real.pi : ℝ) : ℂ)⁻¹ *
        ∑ p ∈ P, c p*heightFourierIntegral (cutoffHeightMultiplier T)
          (Real.log (norm p)-Real.log X) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [smoothLogInterval_eq_height hT,
        Real.log_div (norm_pos_of_ne_zero (hP p hp)).ne' hX.ne']
      ring
    _ = _ := by
      congr 1
      simpa only [id_eq] using height_norm_polynomial_integral P c id _
        (cutoffHeightMultiplier_integrable hT) (Real.log X)

/-- Exact sharp prime interval decomposition, with the endpoint error bound and no assumption about the prime sum itself. -/
theorem prime_sharp_interval_height (P : Finset Eisenstein)
    (hP : ∀ p ∈ P, primaryPrime p) (c : Eisenstein → ℂ)
    {X T : ℝ} (hX : 0 < X) (hT : 0 < T) :
    (∑ p ∈ P, c p*(intervalStep X (2*X) (norm p) : ℂ)) =
      ((2*Real.pi : ℝ) : ℂ)⁻¹ * (∫ t : ℝ,
        (cutoffHeightMultiplier T t * Complex.exp ((-Real.log X*t : ℝ)*Complex.I)) *
          ∑ p ∈ P, c p*normTwist t p) +
      ∑ p ∈ P, c p*sharpIntervalError X T (norm p) := by
  rw [← finite_smooth_interval_height P c hX hT (fun p hp => (hP p hp).2.ne_zero),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  unfold sharpIntervalError
  ring

end CubicFirstMoment

end

end OAI
