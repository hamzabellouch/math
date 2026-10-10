import OAI.Geometry.RCD.Sobolev.DyadicPoissonL2Limit
import OAI.Geometry.RCD.Sobolev.AnnularPoincare
import OAI.Geometry.RCD.Metric.AnnularVolume

namespace OAI

/-! # RCD Poisson value convergence in the established volume regime -/

open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The quarter-error volume regime supplies the annular Poincare
constant and lower volume bound needed for the actual Poisson value limit. -/
theorem rcd_poisson_value_tendsto_zero {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    [IsFiniteMeasureOnCompacts (hausdorff n X)]
    {κ r0 B J C omega : ℝ} {p : X}
    {S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0}
    (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C)
    (hB : 0 ≤ B) (hr01 : r0 ≤ 1) (homega : 0 < omega)
    (hvol : ∀ r : ℝ, 0 < r → r ≤ r0 →
      |(hausdorff n X).real (ball p r) / (omega * r ^ n) - 1| ≤ 1 / 4)
    (hmass : Summable (normalizedDistanceSourceMass (hausdorff n X) hX.quadratic S)) :
    Tendsto (fun i => ‖normalizeLocalL2 (hausdorff n X) (ball p (distanceSourceRadius r0 i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (distanceSourceRadius r0 i))
        (((distanceSourceRadius r0 i) ^ 2)⁻¹ •
          (T.distanceDatum (hausdorff n X) hX.quadratic i - T.replacement i)))‖)
      atTop (𝓝 0) := by
  have hrad (i : ℕ) : distanceSourceRadius r0 i ≤ r0 := by
    have hh := distanceSourceRadius_outer_le S.radius_pos.le i
    have hp := distanceSourceRadius_pos S.radius_pos i
    linarith
  have hlower (i : ℕ) : (3 / 4 * omega) * (distanceSourceRadius r0 i) ^ (n : ℝ) ≤
      (hausdorff n X).real (ball p (distanceSourceRadius r0 i)) := by
    have hr := distanceSourceRadius_pos S.radius_pos i
    have hv := (abs_le.mp (hvol _ hr (hrad i))).1
    have hden : 0 < omega * (distanceSourceRadius r0 i) ^ n := mul_pos homega (pow_pos hr n)
    have hratio : (3 / 4 : ℝ) ≤ (hausdorff n X).real (ball p (distanceSourceRadius r0 i)) /
        (omega * (distanceSourceRadius r0 i) ^ n) := by linarith
    have hh := (le_div_iff₀ hden).mp hratio
    simpa only [Real.rpow_natCast, mul_assoc] using hh
  apply T.value_error_tendsto_zero (hausdorff n X) hX.quadratic
    (annularPoincareConstant_pos K n).le hB (by positivity : 0 < 3 / 4 * omega)
    hlower ?_ hmass
  intro i
  have hr := distanceSourceRadius_pos S.radius_pos i
  have hann := relative_volume_annulus hn hr homega (hvol _ hr (hrad i))
    (hvol _ (mul_pos (by norm_num) hr) (distanceSourceRadius_outer_le S.radius_pos.le i))
  exact hX.annular_dirichlet_poincare hn p hr ((hrad i).trans hr01) hann.1 hann.2

end RegularPointCoordinates

end

end OAI
