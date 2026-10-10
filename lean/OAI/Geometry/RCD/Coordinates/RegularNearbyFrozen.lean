import OAI.Geometry.RCD.Coordinates.RegularHeatFrameGeometry

namespace OAI

/-! # Comparing actual frozen frames at nearby centers -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The existing subball Gram estimate compares the two actual heat
frames. No continuity estimate for an arbitrarily chosen normalizer is
assumed. -/
theorem regular_nearby_frozen_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q z : X} (hq : q ∈ ball base (e.heat.radius / 32))
    (hz : z ∈ ball base (e.heat.radius / 32)) (hzeta : 0 ≤ zeta)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (i : ℕ) (hroom : dist z q ≤ e.heat.radius / 2 ^ (e.heat.shift + i + 17))
    (v : Euclidean n) :
    ‖e.heat.frozenAt z i v‖ ≤ 3 * ‖e.heat.frozenAt q i v‖ := by
  have hgram (w : Euclidean n) :
      (1 / 8 : ℝ) * ⟪w, e.heat.heatAt q (e.heat.shift + i + 17) w⟫_ℝ ≤
        ⟪w, e.heat.heatAt z (e.heat.shift + i + 17) w⟫_ℝ := by
    have hlo := regular_nearby_mean_heat_lower hX e hq hz hzeta hsmall
      (e.heat.shift + i + 16) (by omega)
      (by simpa only [show e.heat.shift + i + 16 + 1 = e.heat.shift + i + 17 by omega] using hroom) w
    rw [show e.heat.shift + i + 16 + 1 = e.heat.shift + i + 17 by omega] at hlo
    have hh := (e.heat.heatMeanComparison z hz (e.heat.shift + i + 17) (by omega) w).1
    change (1 - 1 / 64 : ℝ) * ⟪w,
      (e.heat.meanAt z hz (e.heat.shift + i + 17)).toContinuousLinearMap w⟫_ℝ ≤
        ⟪w, e.heat.heatAt z (e.heat.shift + i + 17) w⟫_ℝ at hh
    simp only [ContinuousLinearEquiv.coe_coe] at hh
    have hp := (e.heat.meanAt_isPositive z hz (e.heat.shift + i + 17)).inner_nonneg_right w
    change 0 ≤ ⟪w, e.heat.meanAt z hz (e.heat.shift + i + 17) w⟫_ℝ at hp
    nlinarith
  have hi := (relative_inverse_bounds
    (e.heat.heatAt q (e.heat.shift + i + 17))
    (e.heat.heatAt z (e.heat.shift + i + 17))
    (e.heat.heatAt_isPositive q _) (e.heat.heatAt_isPositive z _)
    (by norm_num : (0 : ℝ) < 1 / 8) hgram v).1
  have hsq : ‖e.heat.frozenAt z i v‖ ^ 2 ≤ 8 * ‖e.heat.frozenAt q i v‖ ^ 2 := by
    rw [e.heat.frozenAt_norm_sq, e.heat.frozenAt_norm_sq]
    convert hi using 1
    ring
  nlinarith [norm_nonneg (e.heat.frozenAt z i v), norm_nonneg (e.heat.frozenAt q i v)]

/-- Operator-norm form of the same comparison. -/
theorem regular_nearby_frozen_operator {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q z : X} (hq : q ∈ ball base (e.heat.radius / 32))
    (hz : z ∈ ball base (e.heat.radius / 32)) (hzeta : 0 ≤ zeta)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (i : ℕ) (hroom : dist z q ≤ e.heat.radius / 2 ^ (e.heat.shift + i + 17)) :
    ‖(e.heat.frozenAt z i).toContinuousLinearMap.comp
      (e.heat.frozenAt q i).symm.toContinuousLinearMap‖ ≤ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  have h := regular_nearby_frozen_bound hX e hq hz hzeta hsmall i hroom
    ((e.heat.frozenAt q i).symm v)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using h

end RegularPointCoordinates

end

end OAI
