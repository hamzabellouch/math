import OAI.Geometry.RCD.Sobolev.SmallBallPoissonValue
import OAI.Geometry.RCD.Sobolev.ActualPoissonQuadratic

namespace OAI

/-! # The actual quadratic approximation on interior transport balls -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- This is the quantitative quadratic-error field needed by the uniform
sharp-projection family, derived from the full source budget and metric
approximation of the actual coordinate representatives. -/
theorem actual_poisson_small_ball_quadratic_error {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    [IsFiniteMeasureOnCompacts (hausdorff n X)]
    {κ r0 B J C omega eta ε theta : ℝ} {p : X}
    {S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0}
    (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (heta : 0 ≤ eta) (hε : 0 ≤ ε)
    (htheta : 0 < theta) (htheta4 : theta ≤ 1 / 4)
    (hr01 : r0 ≤ 1) (homega : 0 < omega)
    (hvol : ∀ r : ℝ, 0 < r → r ≤ r0 →
      |(hausdorff n X).real (ball p r) / (omega * r ^ n) - 1| ≤ 1 / 4)
    (hsum : Summable (normalizedPoissonDefect (hausdorff n X) hX.quadratic S))
    (hbudget : (∑' j, normalizedPoissonDefect (hausdorff n X) hX.quadratic S j) ≤ eta)
    (i : ℕ) (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (Ccoord : ℝ≥0) (V : X → Euclidean n)
    (hub : ∀ j, ∀ᵐ x ∂hausdorff n X,
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u j) x| ≤ Ccoord)
    (hrep : ∀ j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u j) =ᵐ[
      (hausdorff n X).restrict (ball p (theta * distanceSourceRadius r0 i))]
      fun x => V x j)
    (hmetric : IsPointedApproximation p 0 (distanceSourceRadius r0 i) theta ε V)
    (hcenter : V p = 0) :
    ((hausdorff n X).real (ball p (theta * distanceSourceRadius r0 i)))⁻¹ *
      (∫ x in ball p (theta * distanceSourceRadius r0 i),
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic
          (((distanceSourceRadius r0 i) ^ 2)⁻¹ • T.replacement i) x - ‖V x‖ ^ 2 / 2) ^ 2
        ∂hausdorff n X) ≤
      2 * (((5 / 3 : ℝ) * (theta⁻¹) ^ n) * (annularPoincareConstant K n * B / (3 / 4 * omega) * eta)) +
        2 * (ε * (2 * theta + ε) / 2) ^ 2 := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let r := distanceSourceRadius r0 i
  let Ω := ball p (theta * r)
  let f := (r ^ 2)⁻¹ • T.replacement i
  let q := (r ^ 2)⁻¹ • T.distanceDatum μ hQ i
  let H := coordinateQuadratic μ hQ u Ccoord
  have hr : 0 < r := distanceSourceRadius_pos S.radius_pos i
  have hfin : μ Ω ≠ ∞ := ne_of_lt (hX.finiteOnBounded _ isBounded_ball)
  have hnoise : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (f - q))‖ ^ 2 ≤
      ((5 / 3 : ℝ) * (theta⁻¹) ^ n) * (annularPoincareConstant K n * B / (3 / 4 * omega) * eta) := by
    have hp := rcd_poisson_small_ball_value_error_le hX hn T hκ hB heta htheta
      (htheta4.trans (by norm_num)) hr01 homega hvol hsum hbudget i
    have heq : f - q = -((r ^ 2)⁻¹ • (T.distanceDatum μ hQ i - T.replacement i)) := by
      dsimp only [f, q]
      module
    rw [heq, map_neg]
    simpa only [normalizeLocalL2, smul_neg, norm_neg] using hp
  have hq : SobolevSpace.toLp μ hQ q =ᵐ[μ.restrict Ω]
      fun x => dist p x ^ 2 / (2 * r ^ 2) :=
    ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (mul_le_mul_of_nonneg_right htheta4 hr.le))
      (T.scaled_datum_representative μ hQ i)
  have hb := radial_quadratic_l2_bound μ hQ hr htheta.le hε hfin
    u Ccoord V hub hrep hmetric hcenter f q hq
  have hsquare := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (by positivity : 0 ≤ ε * (2 * theta + ε) / 2))).mpr hb
  have hfinal : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (f - H))‖ ^ 2 ≤
      2 * (((5 / 3 : ℝ) * (theta⁻¹) ^ n) * (annularPoincareConstant K n * B / (3 / 4 * omega) * eta)) +
        2 * (ε * (2 * theta + ε) / 2) ^ 2 := by
    have hc := sq_nonneg (‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (f - q))‖ -
      ε * (2 * theta + ε) / 2)
    change ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (f - H))‖ ≤ _ at hb
    nlinarith
  have hmean : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (f - H))‖ ^ 2 =
      (μ.real Ω)⁻¹ * ∫ x in Ω, (SobolevSpace.toLp μ hQ f x - ‖V x‖ ^ 2 / 2) ^ 2 ∂μ := by
    rw [normalized_sobolev_mean_sq]
    congr 1
    apply integral_congr_ae
    filter_upwards [coordinateQuadratic_eq_norm μ hQ u Ccoord V hub hrep,
      ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ H))]
      with x hx hs
    rw [map_sub, hs, Pi.sub_apply, hx]
  rw [hmean] at hfinal
  exact hfinal

end RegularPointCoordinates

end

end OAI
