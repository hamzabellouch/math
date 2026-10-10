import OAI.Geometry.RCD.Harmonic.RadialBallComparison
import OAI.Geometry.RCD.Coordinates.VolumeProfileRegularity
import OAI.Geometry.RCD.Metric.NonnegativeVolumeComparison

namespace OAI

/-! # A continuous radial comparison profile directly from CD

Continuity of the radial profile gives null spheres directly from the
curvature-dimension condition, before using integrated volume comparison.
-/

open Set Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem FullCD.hyperbolic_radial_ballVolumeComparison
    (μ : Measure X) [SigmaFinite μ] {K : ℝ} {n : ℕ} (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (hK : K < 0) :
    BallVolumeComparison μ (fun r =>
      r * Real.sinh (r * Real.sqrt (-K / ((n : ℝ) - 1))) ^ (n - 1)) := by
  intro p r R hr hrR
  let a := Real.sqrt (-K / ((n : ℝ) - 1))
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hK) (sub_pos.mpr hn1))
  have hR : 0 < R := hr.trans_le hrR
  by_cases heq : r = R
  · simp only [heq, le_refl]
  have hrR' : r < R := lt_of_le_of_ne hrR heq
  have hq : 0 < r / R := div_pos hr hR
  have hq1 : r / R < 1 := (div_lt_one hR).mpr hrR'
  have h := hcd.radial_ball_ratio μ hpos hfin hn hK p hr hrR
  rw [tau_nat_power hn hq hq1, sigma_neg_eq hK hn1 hR] at h
  have hh := ENNReal.toReal_mono (hfin (ball p r) isBounded_ball).ne h
  have hratio : 0 ≤ Real.sinh ((r / R) * R * a) / Real.sinh (R * a) := by
    exact div_nonneg (Real.sinh_pos_iff.mpr (mul_pos (mul_pos hq hR) ha)).le
      (Real.sinh_pos_iff.mpr (mul_pos hR ha)).le
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal hratio] at hh
  rw [div_mul_cancel₀ r hR.ne'] at hh
  have hsR : 0 < Real.sinh (R * a) := Real.sinh_pos_iff.mpr (mul_pos hR ha)
  change (r / R) * (Real.sinh (r * a) / Real.sinh (R * a)) ^ (n - 1) *
    μ.real (ball p R) ≤ μ.real (ball p r) at hh
  change μ.real (ball p R) * (r * Real.sinh (r * a) ^ (n - 1)) ≤
    μ.real (ball p r) * (R * Real.sinh (R * a) ^ (n - 1))
  calc
    μ.real (ball p R) * (r * Real.sinh (r * a) ^ (n - 1)) =
        ((r / R) * (Real.sinh (r * a) / Real.sinh (R * a)) ^ (n - 1) *
          μ.real (ball p R)) * (R * Real.sinh (R * a) ^ (n - 1)) := by
      rw [div_pow]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hh (mul_nonneg hR.le (pow_nonneg hsR.le _))

variable [ProperSpace X]

/-- Every positive-radius sphere is null, without assuming model
Bishop--Gromov in advance. -/
theorem NoncollapsedRCD.sphere_null {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) {r : ℝ} (hr : 0 < r) :
    hausdorff n X (sphere p r) = 0 := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  by_cases hK : 0 ≤ K
  · exact sphere_measure_zero_of_comparison (hX.flat_ballVolumeComparison hn hK)
      (continuous_id.pow n) p hr (pow_pos hr _)
  · have hKneg : K < 0 := lt_of_not_ge hK
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have ha : 0 < Real.sqrt (-K / ((n : ℝ) - 1)) :=
      Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hKneg) (sub_pos.mpr hn1))
    apply sphere_measure_zero_of_comparison
      (hX.cd.hyperbolic_radial_ballVolumeComparison (hausdorff n X) hX.fullSupport
        hX.finiteOnBounded hn hKneg)
    · fun_prop
    · exact hr
    · exact mul_pos hr (pow_pos (Real.sinh_pos_iff.mpr (mul_pos hr ha)) _)

theorem NoncollapsedRCD.closedBall_measure_eq_ball {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) {r : ℝ} (hr : 0 < r) :
    hausdorff n X (closedBall p r) = hausdorff n X (ball p r) := by
  have hz := hX.sphere_null hn p hr
  rw [← closedBall_sdiff_ball, measure_sdiff ball_subset_closedBall
    measurableSet_ball.nullMeasurableSet (hX.finiteOnBounded _ isBounded_ball).ne] at hz
  exact le_antisymm (tsub_eq_zero_iff_le.mp hz) (measure_mono ball_subset_closedBall)

end RegularPointCoordinates

end OAI
