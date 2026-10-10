import OAI.Geometry.RCD.Sobolev.PoissonValueLimit
import OAI.Geometry.RCD.Sobolev.PoissonDefectBudget

namespace OAI

/-! # Uniform Poisson value errors from the total defect budget -/

open Set Metric MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Each actual replacement obeys the same mean-square estimate in terms
of its own full normalized source mass. -/
theorem rcd_poisson_value_error_le {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    [IsFiniteMeasureOnCompacts (hausdorff n X)]
    {κ r0 B J C omega : ℝ} {p : X}
    {S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0}
    (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C)
    (hB : 0 ≤ B) (hr01 : r0 ≤ 1) (homega : 0 < omega)
    (hvol : ∀ r : ℝ, 0 < r → r ≤ r0 →
      |(hausdorff n X).real (ball p r) / (omega * r ^ n) - 1| ≤ 1 / 4) (i : ℕ) :
    ‖normalizeLocalL2 (hausdorff n X) (ball p (distanceSourceRadius r0 i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (distanceSourceRadius r0 i))
        (((distanceSourceRadius r0 i) ^ 2)⁻¹ •
          (T.distanceDatum (hausdorff n X) hX.quadratic i - T.replacement i)))‖ ^ 2 ≤
      (annularPoincareConstant K n * B / (3 / 4 * omega)) *
        normalizedDistanceSourceMass (hausdorff n X) hX.quadratic S i := by
  have hr := distanceSourceRadius_pos S.radius_pos i
  have hrad : distanceSourceRadius r0 i ≤ r0 := by
    have hh := distanceSourceRadius_outer_le S.radius_pos.le i
    linarith
  have hv := (abs_le.mp (hvol _ hr hrad)).1
  have hden : 0 < omega * (distanceSourceRadius r0 i) ^ n := mul_pos homega (pow_pos hr n)
  have hratio : (3 / 4 : ℝ) ≤ (hausdorff n X).real (ball p (distanceSourceRadius r0 i)) /
      (omega * (distanceSourceRadius r0 i) ^ n) := by linarith
  have hlower : (3 / 4 * omega) * (distanceSourceRadius r0 i) ^ (n : ℝ) ≤
      (hausdorff n X).real (ball p (distanceSourceRadius r0 i)) := by
    simpa only [Real.rpow_natCast, mul_assoc] using (le_div_iff₀ hden).mp hratio
  have hann := relative_volume_annulus hn hr homega (hvol _ hr hrad)
    (hvol _ (mul_pos (by norm_num) hr) (distanceSourceRadius_outer_le S.radius_pos.le i))
  exact T.value_error_le_normalized_mass (hausdorff n X) hX.quadratic i
    (annularPoincareConstant_pos K n).le hB (by positivity) hlower
    (hX.annular_dirichlet_poincare hn p hr (hrad.trans hr01) hann.1 hann.2)

/-- The neighborhood's total defect bound controls every individual
Poisson value error uniformly, including the initial scales. -/
theorem rcd_poisson_value_error_le_budget {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    [IsFiniteMeasureOnCompacts (hausdorff n X)]
    {κ r0 B J C omega eta : ℝ} {p : X}
    {S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0}
    (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hr01 : r0 ≤ 1) (homega : 0 < omega)
    (hvol : ∀ r : ℝ, 0 < r → r ≤ r0 →
      |(hausdorff n X).real (ball p r) / (omega * r ^ n) - 1| ≤ 1 / 4)
    (hsum : Summable (normalizedPoissonDefect (hausdorff n X) hX.quadratic S))
    (hbudget : (∑' j, normalizedPoissonDefect (hausdorff n X) hX.quadratic S j) ≤ eta)
    (i : ℕ) :
    ‖normalizeLocalL2 (hausdorff n X) (ball p (distanceSourceRadius r0 i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (distanceSourceRadius r0 i))
        (((distanceSourceRadius r0 i) ^ 2)⁻¹ •
          (T.distanceDatum (hausdorff n X) hX.quadratic i - T.replacement i)))‖ ^ 2 ≤
      (annularPoincareConstant K n * B / (3 / 4 * omega)) * eta := by
  have hmass : normalizedDistanceSourceMass (hausdorff n X) hX.quadratic S i ≤ eta := by
    apply le_trans _ ((hsum.le_tsum i (fun j _ =>
      normalizedPoissonDefect_nonneg (hausdorff n X) hX.quadratic S hκ j)).trans hbudget)
    unfold normalizedPoissonDefect
    apply le_add_of_nonneg_right
    have hr := (distanceSourceRadius_pos S.radius_pos i).le
    positivity
  have hP := (annularPoincareConstant_pos K n).le
  exact (rcd_poisson_value_error_le hX hn T hB hr01 homega hvol i).trans
    (mul_le_mul_of_nonneg_left hmass (by positivity))

end RegularPointCoordinates

end

end OAI
