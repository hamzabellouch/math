import OAI.Geometry.RCD.Coordinates.RegularPatchMassSum

namespace OAI

/-! # Small raw patch mass in the strictly interior heat metric -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Nearby mean forms are at most twice the central heat form. -/
theorem regular_nearby_mean_heat_upper {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q z : X} (hq : q ∈ ball base (e.heat.radius / 32))
    (hz : z ∈ ball base (e.heat.radius / 32)) (hzeta : 0 ≤ zeta)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (i : ℕ) (hi : e.heat.shift ≤ i + 1)
    (hroom : dist z q ≤ e.heat.radius / (2 : ℝ) ^ (i + 1)) (v : Euclidean n) :
    ⟪v, e.heat.meanAt z hz (i + 1) v⟫_ℝ ≤ 2 * ⟪v, e.heat.heatAt q (i + 1) v⟫_ℝ := by
  have hr : 0 < e.heat.radius / (2 : ℝ) ^ i := div_pos e.heat.radius_pos (by positivity)
  have heq : (1 / 2 : ℝ) * (e.heat.radius / (2 : ℝ) ^ i) =
      e.heat.radius / (2 : ℝ) ^ (i + 1) := by rw [pow_succ]; ring
  have hqroom : dist q q + (1 / 2 : ℝ) * (e.heat.radius / (2 : ℝ) ^ i) ≤
      e.heat.radius / (2 : ℝ) ^ i := by rw [dist_self]; linarith
  have hzroom : dist z q + (1 / 2 : ℝ) * (e.heat.radius / (2 : ℝ) ^ i) ≤
      e.heat.radius / (2 : ℝ) ^ i := by rw [heq]; rw [← heq] at hroom; linarith
  have hbq := (regular_subball_mean_comparison hX e hq hq hzeta i
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hqroom v).1
  have hbz := (regular_subball_mean_comparison hX e hq hz hzeta i
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hzroom v).2
  rw [heq] at hbq hbz
  have hheat := (e.heat.heatMeanComparison q hq (i + 1) hi v).1
  have hnonneg := (sobolevMeanGram_isPositive (hausdorff n X) hX.quadratic
    (sobolevColumnMap (hausdorff n X) hX.quadratic e.heat.coordinates)
    (ball q (e.heat.radius / (2 : ℝ) ^ i)) measurableSet_ball).inner_nonneg_right v
  have hmul := mul_le_mul_of_nonneg_right hsmall hnonneg
  change ⟪v, (e.heat.meanAt z hz (i + 1)).toContinuousLinearMap v⟫_ℝ ≤
    2 * ⟪v, e.heat.heatAt q (i + 1) v⟫_ℝ
  rw [e.heat.meanAt_toContinuousLinearMap]
  change _ ≤ 2 * ⟪v, dyadicHeatGramAt (hausdorff n X) hX.quadratic hk
    (sobolevColumnMap (hausdorff n X) hX.quadratic e.heat.coordinates)
    e.heat.cutoff q e.heat.radius_pos e.heat.lambda_pos (i + 1) v⟫_ℝ
  nlinarith

/-- Before conjugation the full raw mass is small in the finer central
heat form. This is the bound needed to charge normalization errors. -/
theorem regular_raw_patch_mass_small {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q z : X} (hq : q ∈ ball base (e.heat.radius / 32))
    (hz : z ∈ ball base (e.heat.radius / 32))
    (hzeta : 0 ≤ zeta) (hzeta1 : zeta ≤ 1) (hCχ : 0 ≤ Cχ)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 2)
    (hnear : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (i : ℕ) (hi : e.heat.shift ≤ i + 15)
    (hroom : dist z q ≤ e.heat.radius / (2 : ℝ) ^ (i + 15)) (v : Euclidean n) :
    let r := e.heat.radius / (2 : ℝ) ^ (i + 15)
    ⟪v, rawPinchingMass e.heat.mass n e.heat.radius z i v⟫_ℝ ≤
      (4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
        (zeta + |K| * r ^ 2)) * ⟪v, e.heat.heatAt q (i + 17) v⟫_ℝ := by
  intro r
  let R := e.heat.meanAt z hz (i + 15)
  let D := rawPinchingMass e.heat.mass n e.heat.radius z i
  have h := regular_pinching_mass_small hX e hz hzeta hzeta1 hCχ hsmall i (R v)
  change ⟪R v, frozenConjugate R D (R v)⟫_ℝ ≤
    pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ * (zeta + |K| * r ^ 2) *
      ⟪R v, R.symm (R v)⟫_ℝ at h
  rw [inner_frozenConjugate, R.symm_apply_apply] at h
  rw [show ⟪R v, v⟫_ℝ = ⟪v, R v⟫_ℝ from real_inner_comm _ _] at h
  have hu := regular_nearby_mean_heat_upper hX e hq hz hzeta hnear (i + 14)
    (by omega) (by simpa only [show i + 14 + 1 = i + 15 by omega] using hroom) v
  rw [show i + 14 + 1 = i + 15 by omega] at hu
  have hs := e.heat.heatAt_two_step_bound hq (i + 15) hi v
  rw [show i + 15 + 2 = i + 17 by omega] at hs
  have hc : 0 ≤ pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
      (zeta + |K| * r ^ 2) := by
    have homega : 0 < euclideanUnitVolume n := euclideanUnitVolume_pos n
    dsimp only [pinchingMassUnitFactor, regularSmallMassCoefficient]
    positivity
  have hbound : ⟪v, R v⟫_ℝ ≤ 4 * ⟪v, e.heat.heatAt q (i + 17) v⟫_ℝ := by
    change ⟪v, e.heat.meanAt z hz (i + 15) v⟫_ℝ ≤ _
    linarith
  have hh := mul_le_mul_of_nonneg_left hbound hc
  exact h.trans (by convert hh using 1; ring)

end RegularPointCoordinates

end

end OAI
