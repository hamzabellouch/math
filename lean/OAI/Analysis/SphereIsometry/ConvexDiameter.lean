import OAI.Analysis.SphereIsometry.DiameterBounds
import Mathlib.Analysis.Normed.Module.Convex

namespace OAI

/-! # Diameter bounds for convex hulls

Convex hulls preserve diameter bounds.
-/

namespace Tingley

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Taking a convex hull preserves a pairwise diameter bound. -/
theorem DiameterLE.convexHull {A : Set E} {δ : ℝ} (h : DiameterLE A δ) :
    DiameterLE (convexHull ℝ A) δ := by
  intro x hx y hy
  obtain ⟨x', hx', y', hy', hxy⟩ := convexHull_exists_dist_ge2 hx hy
  exact hxy.trans (h x' hx' y' hy')

/-- A norm bound on a set also holds on its convex hull. -/
theorem norm_le_of_mem_convexHull {A : Set E} {R : ℝ}
    (hR : ∀ x ∈ A, ‖x‖ ≤ R) {x : E} (hx : x ∈ convexHull ℝ A) : ‖x‖ ≤ R := by
  have hsub : A ⊆ Metric.closedBall (0 : E) R := by
    intro y hy
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR y hy
  have hxball := convexHull_min hsub (convex_closedBall (0 : E) R) hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using hxball

end Tingley

end OAI
