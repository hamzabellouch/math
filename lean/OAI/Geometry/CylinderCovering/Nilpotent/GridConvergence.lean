import OAI.Geometry.CylinderCovering.Convexity.CompactOuterConvergence
import OAI.Geometry.CylinderCovering.Nilpotent.Grid

namespace OAI

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace NilpotentGrid

theorem coarseUnion_subset_cthickening {δ B : ℝ} {D : Set Plane} (hδ : 0 ≤ δ) :
    coarseUnion δ B D ⊆ cthickening (Real.sqrt 2 * δ) D := by
  intro x hx
  obtain ⟨y, hyD, hxy⟩ := coarseUnion_near hδ hx
  apply (closedBall_subset_cthickening hyD (Real.sqrt 2 * δ))
  simpa only [mem_closedBall, dist_eq_norm] using hxy

theorem coarseUnion_excess_tendsto {D : Set Plane} (hD : IsCompact D) (B : ℝ) :
    Tendsto (fun δ : ℝ => volume.real (coarseUnion δ B D \ D))
      (𝓝[>] 0) (𝓝 0) := by
  apply CylinderCovering.CompactOuterConvergence.linear_mesh_real_excess_tendsto
    hD (Real.sqrt 2)
  intro δ hδ
  exact coarseUnion_subset_cthickening hδ.le

end NilpotentGrid

end

end OAI
