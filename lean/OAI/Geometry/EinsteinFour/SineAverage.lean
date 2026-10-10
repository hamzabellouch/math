import OAI.Geometry.EinsteinFour.Averages
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! The exact sine-squared probability weight in the first Dirichlet mode,
its first two moments, and the resulting geodesic averaging coefficient. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

def sineWeight (u : ℝ) : ℝ := 1 - Real.cos (2 * Real.pi * u)

theorem sineWeight_eq (u : ℝ) : sineWeight u = 2 * Real.sin (Real.pi * u) ^ 2 := by
  unfold sineWeight
  rw [mul_assoc, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * u)]

theorem sineWeight_nonneg (u : ℝ) : 0 ≤ sineWeight u := by
  rw [sineWeight_eq]
  positivity

private theorem continuous_sineWeight : Continuous sineWeight := by
  unfold sineWeight
  fun_prop

theorem integral_sineWeight : (∫ u in (0 : ℝ)..1, sineWeight u) = 1 := by
  have hd (u : ℝ) : HasDerivAt
      (fun z => z - Real.sin (2 * Real.pi * z) / (2 * Real.pi)) (sineWeight u) u := by
    convert (hasDerivAt_id u).sub
      ((((hasDerivAt_id u).const_mul (2 * Real.pi)).sin).div_const (2 * Real.pi)) using 1
    all_goals first | rfl | (simp only [sineWeight, id_eq]; field_simp [Real.pi_ne_zero])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (continuous_sineWeight.intervalIntegrable 0 1)]
  simp [Real.sin_two_pi]

theorem integral_sineWeight_first : (∫ u in (0 : ℝ)..1, sineWeight u * u) = 1 / 2 := by
  have hd (u : ℝ) : HasDerivAt
      (fun z => z ^ 2 / 2 - z * Real.sin (2 * Real.pi * z) / (2 * Real.pi) -
        Real.cos (2 * Real.pi * z) / (2 * Real.pi) ^ 2) (sineWeight u * u) u := by
    have hs := ((hasDerivAt_id u).const_mul (2 * Real.pi)).sin
    have hc := ((hasDerivAt_id u).const_mul (2 * Real.pi)).cos
    convert ((((hasDerivAt_id u).pow 2).div_const 2).sub
      (((hasDerivAt_id u).mul hs).div_const (2 * Real.pi))).sub
      (hc.div_const ((2 * Real.pi) ^ 2)) using 1
    all_goals first | rfl | (simp only [sineWeight, id_eq]; field_simp [Real.pi_ne_zero]; ring)
  have hi : IntervalIntegrable (fun u => sineWeight u * u) volume 0 1 :=
    (continuous_sineWeight.mul continuous_id).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi]
  simp [Real.sin_two_pi, Real.cos_two_pi]

theorem integral_sineWeight_second : (∫ u in (0 : ℝ)..1, sineWeight u * u ^ 2) =
    1 / 3 - 1 / (2 * Real.pi ^ 2) := by
  have hd (u : ℝ) : HasDerivAt
      (fun z => z ^ 3 / 3 - z ^ 2 * Real.sin (2 * Real.pi * z) / (2 * Real.pi) -
        2 * z * Real.cos (2 * Real.pi * z) / (2 * Real.pi) ^ 2 +
        2 * Real.sin (2 * Real.pi * z) / (2 * Real.pi) ^ 3)
      (sineWeight u * u ^ 2) u := by
    have hs := ((hasDerivAt_id u).const_mul (2 * Real.pi)).sin
    have hc := ((hasDerivAt_id u).const_mul (2 * Real.pi)).cos
    convert (((((hasDerivAt_id u).pow 3).div_const 3).sub
      ((((hasDerivAt_id u).pow 2).mul hs).div_const (2 * Real.pi))).sub
      ((((hasDerivAt_id u).const_mul 2).mul hc).div_const ((2 * Real.pi) ^ 2))).add
      ((hs.const_mul 2).div_const ((2 * Real.pi) ^ 3)) using 1
    all_goals first | rfl | (simp only [sineWeight, Pi.pow_apply, id_eq]; field_simp [Real.pi_ne_zero]; ring)
  have hi : IntervalIntegrable (fun u => sineWeight u * u ^ 2) volume 0 1 :=
    (continuous_sineWeight.mul (continuous_id.pow 2)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi]
  norm_num [Real.sin_two_pi, Real.cos_two_pi]
  field_simp [Real.pi_ne_zero]

/-- The actual probability measure on the unit time interval, not a moment
axiomatization of that measure. -/
def sineMeasure : Measure ℝ :=
  (volume.restrict (Set.Ioc 0 1)).withDensity (fun u => ENNReal.ofReal (sineWeight u))

theorem integral_sineMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : (∫ u, f u ∂sineMeasure) = ∫ u in (0 : ℝ)..1, sineWeight u • f u := by
  unfold sineMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    continuous_sineWeight.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (sineWeight_nonneg _)]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

instance : IsProbabilityMeasure sineMeasure := by
  apply isProbabilityMeasure_iff_real.mpr
  have h := integral_sineMeasure (fun _ => (1 : ℝ))
  simpa only [integral_const, smul_eq_mul, mul_one, integral_sineWeight] using h

theorem integrable_sineMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Continuous f) : Integrable f sineMeasure := by
  unfold sineMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    continuous_sineWeight.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (sineWeight_nonneg _)]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    ((continuous_sineWeight.smul hf).intervalIntegrable 0 1)

theorem sineMeasure_first : (∫ u, u ∂sineMeasure) = 1 / 2 := by
  simpa only [integral_sineMeasure, smul_eq_mul] using integral_sineWeight_first

theorem sineMeasure_second : (∫ u, u ^ 2 ∂sineMeasure) =
    1 / 3 - 1 / (2 * Real.pi ^ 2) := by
  simpa only [integral_sineMeasure, smul_eq_mul] using integral_sineWeight_second

theorem sineMeasure_variance : (∫ u, u ^ 2 ∂sineMeasure) - (∫ u, u ∂sineMeasure) ^ 2 =
    1 / 12 - 1 / (2 * Real.pi ^ 2) := by
  rw [sineMeasure_first, sineMeasure_second]
  ring

theorem sine_average_coefficient (u : ℝ) :
    (3 / 2) * (Real.pi * u) ^ 2 * (1 / 12 - 1 / (2 * Real.pi ^ 2)) ≤ u ^ 2 / 2 := by
  have hpi : Real.pi ^ 2 < 10 := by
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have heq : (3 / 2) * (Real.pi * u) ^ 2 * (1 / 12 - 1 / (2 * Real.pi ^ 2)) =
      u ^ 2 * ((Real.pi ^ 2 - 6) / 8) := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [heq]
  nlinarith [mul_nonneg (sq_nonneg u) (show 0 ≤ 10 - Real.pi ^ 2 by linarith)]

/-- The averaged squared norm retained by the first sine mode. For the
curvature application the increment hypothesis comes from the invariant
geodesic-flow measure and the integrated Weyl differential identity. -/
theorem sine_average_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {A : ℝ → E} {q u : ℝ} (hq : 0 ≤ q)
    (hA : Integrable A sineMeasure)
    (hA2 : Integrable (fun t => ‖A t‖ ^ 2) sineMeasure)
    (hstationary : ∀ᵐ t ∂sineMeasure, ‖A t‖ ^ 2 = q)
    (hincrement : ∀ s t, ‖A s - A t‖ ^ 2 ≤
      ((3 / 2) * q * (Real.pi * u) ^ 2) * (s - t) ^ 2) :
    q * (1 - u ^ 2 / 2) ≤ ‖∫ t, A t ∂sineMeasure‖ ^ 2 := by
  have h := stationary_average_lower hA hA2 (integrable_sineMeasure continuous_id)
    (integrable_sineMeasure (continuous_id.pow 2)) hstationary hincrement
  rw [sineMeasure_variance] at h
  have hc := mul_le_mul_of_nonneg_left (sine_average_coefficient u) hq
  nlinarith only [h, hc]

/-- The differentiable-curve version supplies both integrability and the
increment estimate. Its derivative hypothesis has exactly the geodesic
curvature normalization after time is rescaled to the unit interval. -/
theorem sine_average_lower_of_derivative {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {A d : ℝ → E} {q u : ℝ} (hq : 0 ≤ q)
    (hd : ∀ t, HasDerivAt A (d t) t)
    (hstationary : ∀ᵐ t ∂sineMeasure, ‖A t‖ ^ 2 = q)
    (hbound : ∀ t, ‖d t‖ ^ 2 ≤ (3 / 2) * q * (Real.pi * u) ^ 2) :
    q * (1 - u ^ 2 / 2) ≤ ‖∫ t, A t ∂sineMeasure‖ ^ 2 := by
  have hA : Continuous A := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  apply sine_average_lower hq (integrable_sineMeasure hA)
    (integrable_sineMeasure (hA.norm.pow 2)) hstationary
  exact increment_bound_of_derivative (by positivity) hd hbound

end

end PositiveEinsteinFour.Averages

end OAI
