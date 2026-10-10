import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceDirectionJet

namespace OAI

/-! Scale bounds for a remainder with vanishing value and first derivative.
The second derivative bound tends to zero for a flat second jet. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma flat_first_derivative_bound {R : Base → ProjectionTarget 3}
    (hR : ContDiff ℝ ∞ R) (hD0 : fderiv ℝ R 0 = 0)
    {r M : ℝ} (hr : 0 ≤ r)
    (hb : ∀ x ∈ Metric.closedBall (0 : Base) r, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ M)
    {x : Base} (hx : x ∈ Metric.closedBall (0 : Base) r) :
    ‖fderiv ℝ R x‖ ≤ M*‖x‖ := by
  have hd : ∀ y ∈ Metric.closedBall (0 : Base) r, DifferentiableAt ℝ (fderiv ℝ R) y :=
    fun y _ => (hR.fderiv_right (m := ∞) (by simp)).differentiable (by simp) y
  have h := (convex_closedBall (0 : Base) r).norm_image_sub_le_of_norm_fderiv_le
    hd hb (Metric.mem_closedBall_self hr) hx
  simpa only [hD0,sub_zero] using h

lemma flat_value_bound {R : Base → ProjectionTarget 3}
    (hR : ContDiff ℝ ∞ R) (h0 : R 0 = 0) (hD0 : fderiv ℝ R 0 = 0)
    {r M : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hb : ∀ x ∈ Metric.closedBall (0 : Base) r, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ M)
    {x : Base} (hx : x ∈ Metric.closedBall (0 : Base) r) :
    ‖R x‖ ≤ M*r*‖x‖ := by
  have hD : ∀ y ∈ Metric.closedBall (0 : Base) r, ‖fderiv ℝ R y‖ ≤ M*r := by
    intro y hy
    apply (flat_first_derivative_bound hR hD0 hr hb hy).trans
    exact mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy) hM
  have h := (convex_closedBall (0 : Base) r).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hR.differentiable (by simp) y) hD (Metric.mem_closedBall_self hr) hx
  simpa only [h0,sub_zero] using h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
