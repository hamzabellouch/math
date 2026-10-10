import OAI.Geometry.RCD.Coordinates.DyadicRadialFits
import OAI.Geometry.RCD.Coordinates.NormalizedDirichletError

namespace OAI

/-! # Mean-square value error of the actual dyadic Poisson replacements -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- The source-energy estimate and Dirichlet Poincare give the exact
normalized squared-distance value error, including the full source mass. -/
theorem DyadicDistanceReplacements.normalized_value_error
    {n : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    {P : ℝ} (hP : 0 ≤ P)
    (hvol : 0 < μ.real (ball p (distanceSourceRadius r0 i)))
    (hpoin : ∀ v : SobolevSpace.dirichlet μ hQ (ball p (distanceSourceRadius r0 i)),
      ‖SobolevSpace.toLp μ hQ v.val‖ ^ 2 ≤ P * (distanceSourceRadius r0 i) ^ 2 *
        energyForm μ hQ v.val v.val) :
    ‖normalizeLocalL2 μ (ball p (distanceSourceRadius r0 i))
      (ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt
        (isCompact_closedBall p _).measure_lt_top))
      (SobolevSpace.restrictLp μ hQ (ball p (distanceSourceRadius r0 i))
        (((distanceSourceRadius r0 i) ^ 2)⁻¹ • (T.distanceDatum μ hQ i - T.replacement i)))‖ ^ 2 ≤
      P * B * ((S.source i).real (ball p (distanceSourceRadius r0 i)) /
        μ.real (ball p (distanceSourceRadius r0 i))) := by
  let r := distanceSourceRadius r0 i
  let Ω := ball p r
  let H := T.distanceDatum μ hQ i - T.replacement i
  have hr : 0 < r := distanceSourceRadius_pos S.radius_pos i
  have hfin : μ Ω ≠ ∞ := ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt
    (isCompact_closedBall p r).measure_lt_top)
  have hv0 : μ.real Ω ≠ 0 := hvol.ne'
  have hdir : H ∈ SobolevSpace.dirichlet μ hQ Ω := by
    simpa only [H, DyadicDistanceReplacements.distanceDatum, neg_sub] using (SobolevSpace.dirichlet μ hQ Ω).neg_mem (T.boundary i)
  let E := B * ((S.source i).real Ω / μ.real Ω)
  have henergy : (∫ x, (SobolevSpace.minimalSlope μ hQ H x) ^ 2 ∂μ) ≤
      E * r ^ 2 * μ.real Ω := by
    have ht := T.energy_error i
    change (∫ x, (SobolevSpace.minimalSlope μ hQ H x) ^ 2 ∂μ) ≤
      (S.source i).real Ω * (B * r ^ 2) at ht
    apply ht.trans_eq
    dsimp only [E]
    field_simp [hv0]
  have hb := normalized_dirichlet_error μ hQ Ω hfin hvol hr hP H hdir hpoin henergy
  convert hb using 1
  dsimp only [E]
  ring

end RegularPointCoordinates

end

end OAI
