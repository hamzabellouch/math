import OAI.Geometry.RCD.Sobolev.PoissonUniformValue
import OAI.Geometry.RCD.Coordinates.RadialFitRestriction

namespace OAI

/-! # Uniform Poisson values on the interior compactness ball -/

open Set Metric MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

private theorem quarter_volume_ratio {n : ℕ} {r omega V W : ℝ}
    (hr : 0 < r) (homega : 0 < omega)
    (hV : |V / (omega * r ^ n) - 1| ≤ 1 / 4)
    (hW : |W / (omega * (r / 4) ^ n) - 1| ≤ 1 / 4) :
    0 < V ∧ 0 < W ∧ V ≤ ((5 / 3 : ℝ) * 4 ^ n) * W := by
  have hvr : 0 < omega * r ^ n := mul_pos homega (pow_pos hr _)
  have hwr : 0 < omega * (r / 4) ^ n := mul_pos homega (pow_pos (by positivity) _)
  have hvlo : (3 / 4 : ℝ) * (omega * r ^ n) ≤ V := by
    apply (le_div_iff₀ hvr).mp
    linarith [(abs_le.mp hV).1]
  have hvhi : V ≤ (5 / 4 : ℝ) * (omega * r ^ n) := by
    apply (div_le_iff₀ hvr).mp
    linarith [(abs_le.mp hV).2]
  have hwlo : (3 / 4 : ℝ) * (omega * (r / 4) ^ n) ≤ W := by
    apply (le_div_iff₀ hwr).mp
    linarith [(abs_le.mp hW).1]
  have hpow : (4 : ℝ) ^ n * (r / 4) ^ n = r ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_left hwlo (by positivity : 0 ≤ (5 / 3 : ℝ) * 4 ^ n)
  have hscale : ((5 / 3 : ℝ) * 4 ^ n) * ((3 / 4) * (omega * (r / 4) ^ n)) =
      (5 / 4 : ℝ) * (omega * r ^ n) := by
    calc
      _ = (5 / 4 : ℝ) * omega * ((4 : ℝ) ^ n * (r / 4) ^ n) := by ring
      _ = _ := by rw [hpow]; ring
  rw [hscale] at hmul
  exact ⟨(mul_pos (by norm_num) hvr).trans_le hvlo,
    (mul_pos (by norm_num) hwr).trans_le hwlo, hvhi.trans hmul⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Restriction of the actual replacement to the interior quarter ball
preserves a uniform error bound. Only the explicit Euclidean volume ratio
is lost; the bound is independent of the center and dyadic index. -/
theorem rcd_poisson_interior_value_error_le {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    [IsFiniteMeasureOnCompacts (hausdorff n X)]
    {κ r0 B J C omega eta : ℝ} {p : X}
    {S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0}
    (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (heta : 0 ≤ eta) (hr01 : r0 ≤ 1) (homega : 0 < omega)
    (hvol : ∀ r : ℝ, 0 < r → r ≤ r0 →
      |(hausdorff n X).real (ball p r) / (omega * r ^ n) - 1| ≤ 1 / 4)
    (hsum : Summable (normalizedPoissonDefect (hausdorff n X) hX.quadratic S))
    (hbudget : (∑' j, normalizedPoissonDefect (hausdorff n X) hX.quadratic S j) ≤ eta)
    (i : ℕ) :
    ‖normalizeLocalL2 (hausdorff n X) (ball p (distanceSourceRadius r0 i / 4))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (distanceSourceRadius r0 i / 4))
        (((distanceSourceRadius r0 i) ^ 2)⁻¹ •
          (T.distanceDatum (hausdorff n X) hX.quadratic i - T.replacement i)))‖ ^ 2 ≤
      ((5 / 3 : ℝ) * 4 ^ n) *
        ((annularPoincareConstant K n * B / (3 / 4 * omega)) * eta) := by
  have hr := distanceSourceRadius_pos S.radius_pos i
  have hrad : distanceSourceRadius r0 i ≤ r0 := by
    have hh := distanceSourceRadius_outer_le S.radius_pos.le i
    linarith
  have hquarter : distanceSourceRadius r0 i / 4 ≤ r0 := le_trans (by linarith) hrad
  obtain ⟨houter, hinner, hratio⟩ := quarter_volume_ratio hr homega
    (hvol _ hr hrad) (hvol _ (by positivity) hquarter)
  have hP := (annularPoincareConstant_pos K n).le
  exact normalized_fit_restrict_sq (hausdorff n X) hX.quadratic
    (ball_subset_ball (by linarith)) _ _ houter hinner _
    (by positivity : 0 ≤ (annularPoincareConstant K n * B / (3 / 4 * omega)) * eta)
    hratio (rcd_poisson_value_error_le_budget hX hn T hκ hB hr01 homega hvol hsum hbudget i)

end RegularPointCoordinates

end

end OAI
