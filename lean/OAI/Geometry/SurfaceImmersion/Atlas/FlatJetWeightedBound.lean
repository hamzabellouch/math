import OAI.Geometry.SurfaceImmersion.Geometry.FlatSecondJetBounds
import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds

namespace OAI

/-! A flat remainder has a scale-weighted second-order bound controlled
only by its second derivative on the coordinate ball. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem flat_remainder_weighted_bound {R : Base → ProjectionTarget 3}
    (hR : ContDiff ℝ ∞ R) (h0 : R 0 = 0) (hD0 : fderiv ℝ R 0 = 0)
    {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hb : ∀ x ∈ Metric.closedBall (0 : Base) r, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ M) :
    WeightedEstimates.WeightedBound (Metric.ball (0 : Base) r) r 2 (M*r^2) R := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j isOpen_ball hx]
  have hx' : x ∈ Metric.closedBall (0 : Base) r := Metric.ball_subset_closedBall hx
  have hxr : ‖x‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx'
  interval_cases j
  · rw [pow_zero,one_mul,norm_iteratedFDeriv_zero]
    apply (flat_value_bound hR h0 hD0 hr.le hM hb hx').trans
    calc
      M*r*‖x‖ ≤ M*r*r := mul_le_mul_of_nonneg_left hxr (mul_nonneg hM hr.le)
      _ = M*r^2 := by ring
  · rw [pow_one,norm_iteratedFDeriv_one]
    have hd := flat_first_derivative_bound hR hD0 hr.le hb hx'
    calc
      r*‖fderiv ℝ R x‖ ≤ r*(M*‖x‖) := mul_le_mul_of_nonneg_left hd hr.le
      _ = M*r*‖x‖ := by ring
      _ ≤ M*r*r := mul_le_mul_of_nonneg_left hxr (mul_nonneg hM hr.le)
      _ = M*r^2 := by ring
  · rw [← norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one]
    exact (mul_le_mul_of_nonneg_left (hb x hx') (sq_nonneg r)).trans_eq (mul_comm _ _)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
