import OAI.Geometry.RCD.Sobolev.DyadicPoissonValueError
import OAI.Geometry.RCD.Metric.DistanceSourceBudget

namespace OAI

/-! # Strong radial value convergence from the full dyadic source budget -/

open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- A Euclidean lower volume bound converts the full-source mean-square
estimate to exactly the normalized source mass already known to be summable. -/
theorem DyadicDistanceReplacements.value_error_le_normalized_mass
    {n : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    {P nu : ℝ} (hP : 0 ≤ P) (hB : 0 ≤ B) (hnu : 0 < nu)
    (hvol : nu * (distanceSourceRadius r0 i) ^ (n : ℝ) ≤
      μ.real (ball p (distanceSourceRadius r0 i)))
    (hpoin : ∀ v : SobolevSpace.dirichlet μ hQ (ball p (distanceSourceRadius r0 i)),
      ‖SobolevSpace.toLp μ hQ v.val‖ ^ 2 ≤ P * (distanceSourceRadius r0 i) ^ 2 *
        energyForm μ hQ v.val v.val) :
    ‖normalizeLocalL2 μ (ball p (distanceSourceRadius r0 i))
      (ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt
        (isCompact_closedBall p _).measure_lt_top))
      (SobolevSpace.restrictLp μ hQ (ball p (distanceSourceRadius r0 i))
        (((distanceSourceRadius r0 i) ^ 2)⁻¹ • (T.distanceDatum μ hQ i - T.replacement i)))‖ ^ 2 ≤
      (P * B / nu) * normalizedDistanceSourceMass μ hQ S i := by
  have hr := distanceSourceRadius_pos S.radius_pos i
  have hp := Real.rpow_pos_of_pos hr (n : ℝ)
  have hvolpos := lt_of_lt_of_le (mul_pos hnu hp) hvol
  have hb := T.normalized_value_error μ hQ i hP hvolpos hpoin
  apply hb.trans
  apply (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left (show 0 ≤ (S.source i).real (ball p (distanceSourceRadius r0 i)) from
      measureReal_nonneg) (mul_pos hnu hp) hvol) (mul_nonneg hP hB)).trans_eq
  unfold normalizedDistanceSourceMass
  rw [Real.rpow_neg hr.le]
  field_simp

/-- The actual rescaled replacements converge in mean square to squared
distance when the full dyadic source masses are summable. -/
theorem DyadicDistanceReplacements.value_error_tendsto_zero
    {n : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C)
    {P nu : ℝ} (hP : 0 ≤ P) (hB : 0 ≤ B) (hnu : 0 < nu)
    (hvol : ∀ i, nu * (distanceSourceRadius r0 i) ^ (n : ℝ) ≤
      μ.real (ball p (distanceSourceRadius r0 i)))
    (hpoin : ∀ i, ∀ v : SobolevSpace.dirichlet μ hQ (ball p (distanceSourceRadius r0 i)),
      ‖SobolevSpace.toLp μ hQ v.val‖ ^ 2 ≤ P * (distanceSourceRadius r0 i) ^ 2 *
        energyForm μ hQ v.val v.val)
    (hmass : Summable (normalizedDistanceSourceMass μ hQ S)) :
    Tendsto (fun i => ‖normalizeLocalL2 μ (ball p (distanceSourceRadius r0 i))
      (ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt
        (isCompact_closedBall p _).measure_lt_top))
      (SobolevSpace.restrictLp μ hQ (ball p (distanceSourceRadius r0 i))
        (((distanceSourceRadius r0 i) ^ 2)⁻¹ • (T.distanceDatum μ hQ i - T.replacement i)))‖)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun i => Real.le_sqrt_of_sq_le
      (T.value_error_le_normalized_mass μ hQ i hP hB hnu (hvol i) (hpoin i)))
  simpa using ((tendsto_const_nhds (x := P * B / nu)).mul hmass.tendsto_atTop_zero).sqrt

end RegularPointCoordinates

end

end OAI
