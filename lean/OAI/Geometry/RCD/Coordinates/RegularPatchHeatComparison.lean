import OAI.Geometry.RCD.Coordinates.RegularPinchingSmallness
import OAI.Geometry.RCD.Coordinates.RegularFrozenMetrics

namespace OAI

/-! # Actual heat comparison across the full support of a pinching patch -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- One outer normalized ball compares every mean whose center can lie
in the support of the actual patch. The mean radius is 1/64 of that ball. -/
theorem regular_patch_mean_heat_lower {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q z : X} (hq : q ∈ ball base (e.heat.radius / 32))
    (hz : z ∈ ball base (e.heat.radius / 32)) (hzeta : 0 ≤ zeta)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 64 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (i : ℕ) (hi : e.heat.shift ≤ i + 15)
    (hroom : dist z q ≤ 32 * (e.heat.radius / (2 : ℝ) ^ (i + 15))) (v : Euclidean n) :
    (1 / 4 : ℝ) * ⟪v, e.heat.heatAt q (i + 15) v⟫_ℝ ≤
      ⟪v, e.heat.meanAt z hz (i + 15) v⟫_ℝ := by
  let r := e.heat.radius / (2 : ℝ) ^ (i + 15)
  have hr : 0 < r := div_pos e.heat.radius_pos (by positivity)
  have hout : e.heat.radius / (2 : ℝ) ^ (i + 9) = 64 * r := by
    dsimp only [r]
    rw [show i + 15 = (i + 9) + 6 by omega, pow_add]
    norm_num
    ring
  have heq : (1 / 64 : ℝ) * (e.heat.radius / (2 : ℝ) ^ (i + 9)) = r := by
    rw [hout]; ring
  have hqroom : dist q q + (1 / 64 : ℝ) * (e.heat.radius / (2 : ℝ) ^ (i + 9)) ≤
      e.heat.radius / (2 : ℝ) ^ (i + 9) := by rw [dist_self, heq, hout]; linarith
  have hzroom : dist z q + (1 / 64 : ℝ) * (e.heat.radius / (2 : ℝ) ^ (i + 9)) ≤
      e.heat.radius / (2 : ℝ) ^ (i + 9) := by rw [heq, hout]; change dist z q ≤ 32 * r at hroom; linarith
  have hbq := (regular_subball_mean_comparison hX e hq hq hzeta (i + 9)
    (by norm_num : (0 : ℝ) < 1 / 64) (by norm_num) hqroom v).2
  have hbz := (regular_subball_mean_comparison hX e hq hz hzeta (i + 9)
    (by norm_num : (0 : ℝ) < 1 / 64) (by norm_num) hzroom v).1
  rw [heq] at hbq hbz
  have hheat := (e.heat.heatMeanComparison q hq (i + 15) hi v).2
  have hnonneg := (sobolevMeanGram_isPositive (hausdorff n X) hX.quadratic
    (sobolevColumnMap (hausdorff n X) hX.quadratic e.heat.coordinates)
    (ball q (e.heat.radius / (2 : ℝ) ^ (i + 9))) measurableSet_ball).inner_nonneg_right v
  have hmul := mul_le_mul_of_nonneg_right hsmall hnonneg
  change (1 / 4 : ℝ) * ⟪v, e.heat.heatAt q (i + 15) v⟫_ℝ ≤
    ⟪v, (e.heat.meanAt z hz (i + 15)).toContinuousLinearMap v⟫_ℝ
  rw [e.heat.meanAt_toContinuousLinearMap]
  change (1 / 4 : ℝ) * ⟪v, dyadicHeatGramAt (hausdorff n X) hX.quadratic hk
    (sobolevColumnMap (hausdorff n X) hX.quadratic e.heat.coordinates)
    e.heat.cutoff q e.heat.radius_pos e.heat.lambda_pos (i + 15) v⟫_ℝ ≤ _
  change ⟪v, dyadicHeatGramAt (hausdorff n X) hX.quadratic hk
    (sobolevColumnMap (hausdorff n X) hX.quadratic e.heat.coordinates)
    e.heat.cutoff q e.heat.radius_pos e.heat.lambda_pos (i + 15) v⟫_ℝ ≤
      (1 + 1 / 64 : ℝ) * ⟪v, sobolevMeanGram (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic e.heat.coordinates)
        (ball q r) measurableSet_ball v⟫_ℝ at hheat
  nlinarith

/-- The full patch mass is small in the heat metric at the testing point,
even when the patch center is thirty-two mean radii away. -/
theorem regular_patch_mass_small {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q z : X} (hq : q ∈ ball base (e.heat.radius / 32))
    (hz : z ∈ ball base (e.heat.radius / 32))
    (hzeta : 0 ≤ zeta) (hzeta1 : zeta ≤ 1) (hCχ : 0 ≤ Cχ)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 2)
    (hnear : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 64 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (i : ℕ) (hi : e.heat.shift ≤ i + 15)
    (hroom : dist z q ≤ 32 * (e.heat.radius / (2 : ℝ) ^ (i + 15))) (xi : Euclidean n) :
    let r := e.heat.radius / (2 : ℝ) ^ (i + 15)
    ⟪xi, e.heat.pinchingMassMatrix z hz i xi⟫_ℝ ≤
      4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
        (zeta + |K| * r ^ 2) * ⟪xi, (e.heat.heatAt q (i + 15)).symm xi⟫_ℝ := by
  intro r
  have hm := regular_pinching_mass_small hX e hz hzeta hzeta1 hCχ hsmall i xi
  have hcomp := (relative_inverse_bounds (e.heat.heatAt q (i + 15))
    (e.heat.meanAt z hz (i + 15)) (e.heat.heatAt_isPositive q (i + 15))
    (e.heat.meanAt_isPositive z hz (i + 15)) (by norm_num : (0 : ℝ) < 1 / 4)
    (regular_patch_mean_heat_lower hX e hq hz hzeta hnear i hi hroom) xi).1
  have hcoeff : 0 ≤ pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
      (zeta + |K| * r ^ 2) := by
    have homega : 0 < euclideanUnitVolume n := euclideanUnitVolume_pos n
    dsimp only [pinchingMassUnitFactor, regularSmallMassCoefficient]
    positivity
  have h := mul_le_mul_of_nonneg_left hcomp hcoeff
  norm_num at h
  exact hm.trans (by convert h using 1; ring)

end RegularPointCoordinates

end

end OAI
