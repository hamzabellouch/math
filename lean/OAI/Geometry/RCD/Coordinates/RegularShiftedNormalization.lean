import OAI.Geometry.RCD.Coordinates.RegularFrozenMetrics

namespace OAI

/-! # Normalization errors for a strictly interior heat scale -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Changing from the patch mean to a heat scale two steps finer costs a
mean-normalization error and a telescoping heat increment. -/
theorem regular_shifted_inverse_error {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q z : X} (hq : q ∈ ball base (e.heat.radius / 32))
    (hz : z ∈ ball base (e.heat.radius / 32)) (hzeta : 0 ≤ zeta)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (i : ℕ) (hi : e.heat.shift ≤ i + 15)
    (hroom : dist z q ≤ e.heat.radius / (2 : ℝ) ^ (i + 15))
    (henlargement : dist q z ≤ enlargement * (e.heat.radius / (2 : ℝ) ^ (i + 15)))
    (xi : Euclidean n) :
    let P := e.heat.heatAt q (i + 15)
    let Q := e.heat.heatAt q (i + 17)
    let R := e.heat.meanAt z hz (i + 15)
    let F := dyadicBochnerEnvelope e.heat.mass n q e.heat.radius (i + 15)
    let delta := R.symm xi - Q.symm xi
    ⟪delta, Q delta⟫_ℝ ≤
      32 * e.heat.comparisonConstant * ⟪P.symm xi, F (P.symm xi)⟫_ℝ +
        2 * (⟪xi, Q.symm xi⟫_ℝ - ⟪xi, P.symm xi⟫_ℝ) := by
  intro P Q R F delta
  have hmean := regular_inverse_mean_heat_error hX e hq hz hzeta hsmall
    (i + 14) (by omega) (by simpa only [show i + 14 + 1 = i + 15 by omega] using hroom)
    (by simpa only [show i + 14 + 1 = i + 15 by omega] using henlargement) xi
  change ⟪R.symm xi - P.symm xi, P (R.symm xi - P.symm xi)⟫_ℝ ≤
    16 * e.heat.comparisonConstant * ⟪P.symm xi, F (P.symm xi)⟫_ℝ at hmean
  have hinc := e.heat.heatAt_two_step_inverse_error hq (i + 15) hi xi
  rw [show i + 15 + 2 = i + 17 by omega] at hinc
  change ⟪Q.symm xi - P.symm xi, Q (Q.symm xi - P.symm xi)⟫_ℝ ≤
    ⟪xi, Q.symm xi⟫_ℝ - ⟪xi, P.symm xi⟫_ℝ at hinc
  have hdec := (e.heat.heatAt_two_step_decrement_positive hq (i + 15) hi).inner_nonneg_right
    (R.symm xi - P.symm xi)
  rw [show i + 15 + 2 = i + 17 by omega] at hdec
  change 0 ≤ ⟪R.symm xi - P.symm xi,
    (P.toContinuousLinearMap - Q.toContinuousLinearMap) (R.symm xi - P.symm xi)⟫_ℝ at hdec
  simp only [sub_apply, inner_sub_right, ContinuousLinearEquiv.coe_coe] at hdec
  have hadd := positive_form_add_le_two (e.heat.heatAt_isPositive q (i + 17))
    (R.symm xi - P.symm xi) (-(Q.symm xi - P.symm xi))
  have heq : R.symm xi - P.symm xi + -(Q.symm xi - P.symm xi) = delta := by dsimp only [delta]; abel
  rw [heq] at hadd
  change ⟪delta, Q delta⟫_ℝ ≤
    2 * ⟪R.symm xi - P.symm xi, Q (R.symm xi - P.symm xi)⟫_ℝ +
    2 * ⟪-(Q.symm xi - P.symm xi), Q (-(Q.symm xi - P.symm xi))⟫_ℝ at hadd
  simp only [map_neg, inner_neg_left, inner_neg_right, neg_neg] at hadd
  linarith

end RegularPointCoordinates

end

end OAI
