import OAI.Geometry.RCD.Sobolev.PoissonInteriorValues

namespace OAI

/-! # Poisson value errors on the smaller balls used by two-center transport -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

private theorem relative_ball_volume_ratio {r theta omega V W : ℝ} {n : ℕ}
    (hr : 0 < r) (htheta : 0 < theta) (homega : 0 < omega)
    (hV : |V / (omega * r ^ n) - 1| ≤ 1 / 4)
    (hW : |W / (omega * (theta * r) ^ n) - 1| ≤ 1 / 4) :
    0 < V ∧ 0 < W ∧ V ≤ ((5 / 3 : ℝ) * (theta⁻¹) ^ n) * W := by
  have hvr : 0 < omega * r ^ n := mul_pos homega (pow_pos hr _)
  have hwr : 0 < omega * (theta * r) ^ n := mul_pos homega (pow_pos (mul_pos htheta hr) _)
  have hvlo : (3 / 4 : ℝ) * (omega * r ^ n) ≤ V := by
    apply (le_div_iff₀ hvr).mp
    linarith [(abs_le.mp hV).1]
  have hvhi : V ≤ (5 / 4 : ℝ) * (omega * r ^ n) := by
    apply (div_le_iff₀ hvr).mp
    linarith [(abs_le.mp hV).2]
  have hwlo : (3 / 4 : ℝ) * (omega * (theta * r) ^ n) ≤ W := by
    apply (le_div_iff₀ hwr).mp
    linarith [(abs_le.mp hW).1]
  have hpow : (theta⁻¹) ^ n * (theta * r) ^ n = r ^ n := by
    rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ htheta.ne', one_mul]
  have hmul := mul_le_mul_of_nonneg_left hwlo
    (by positivity : 0 ≤ (5 / 3 : ℝ) * (theta⁻¹) ^ n)
  have hscale : ((5 / 3 : ℝ) * (theta⁻¹) ^ n) *
      ((3 / 4) * (omega * (theta * r) ^ n)) = (5 / 4 : ℝ) * (omega * r ^ n) := by
    calc
      _ = (5 / 4 : ℝ) * omega * ((theta⁻¹) ^ n * (theta * r) ^ n) := by ring
      _ = _ := by rw [hpow]; ring
  rw [hscale] at hmul
  exact ⟨(mul_pos (by norm_num) hvr).trans_le hvlo,
    (mul_pos (by norm_num) hwr).trans_le hwlo, hvhi.trans hmul⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The same actual source budget controls every fixed smaller interior
ball; the explicit volume loss is the only dependence on its radius ratio. -/
theorem rcd_poisson_small_ball_value_error_le {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    [IsFiniteMeasureOnCompacts (hausdorff n X)]
    {κ r0 B J C omega eta theta : ℝ} {p : X}
    {S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0}
    (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (heta : 0 ≤ eta)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) (hr01 : r0 ≤ 1) (homega : 0 < omega)
    (hvol : ∀ r : ℝ, 0 < r → r ≤ r0 →
      |(hausdorff n X).real (ball p r) / (omega * r ^ n) - 1| ≤ 1 / 4)
    (hsum : Summable (normalizedPoissonDefect (hausdorff n X) hX.quadratic S))
    (hbudget : (∑' j, normalizedPoissonDefect (hausdorff n X) hX.quadratic S j) ≤ eta)
    (i : ℕ) :
    ‖normalizeLocalL2 (hausdorff n X) (ball p (theta * distanceSourceRadius r0 i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball p (theta * distanceSourceRadius r0 i))
        (((distanceSourceRadius r0 i) ^ 2)⁻¹ •
          (T.distanceDatum (hausdorff n X) hX.quadratic i - T.replacement i)))‖ ^ 2 ≤
      ((5 / 3 : ℝ) * (theta⁻¹) ^ n) *
        ((annularPoincareConstant K n * B / (3 / 4 * omega)) * eta) := by
  have hr := distanceSourceRadius_pos S.radius_pos i
  have hrad : distanceSourceRadius r0 i ≤ r0 := by
    have hh := distanceSourceRadius_outer_le S.radius_pos.le i
    linarith
  have hthetaR : theta * distanceSourceRadius r0 i ≤ distanceSourceRadius r0 i :=
    mul_le_of_le_one_left hr.le htheta1
  obtain ⟨houter, hinner, hratio⟩ := relative_ball_volume_ratio hr htheta homega
    (hvol _ hr hrad) (hvol _ (mul_pos htheta hr) (hthetaR.trans hrad))
  have hP := (annularPoincareConstant_pos K n).le
  exact normalized_fit_restrict_sq (hausdorff n X) hX.quadratic
    (ball_subset_ball hthetaR) _ _ houter hinner _
    (by positivity : 0 ≤ (annularPoincareConstant K n * B / (3 / 4 * omega)) * eta)
    hratio (rcd_poisson_value_error_le_budget hX hn T hκ hB hr01 homega hvol hsum hbudget i)

end RegularPointCoordinates

end

end OAI
