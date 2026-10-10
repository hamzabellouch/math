import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.BundleMinimizerCompactness

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

omit [IsRiemannianManifold (model n) M] in
 theorem tangent_disk_compact (R : ℝ) :
    IsCompact {p : TangentBundle (model n) M | ‖p.2‖ ≤ R} := by
  classical
  choose V hV hxV K hK hbound using (fun x : M => locally_compact_tangent_bound (n := n) x R)
  obtain ⟨F,hF⟩ := isCompact_univ.elim_finite_subcover V hV (fun x _ => mem_iUnion.mpr ⟨x,hxV x⟩)
  have hbig : IsCompact (⋃ x ∈ F, K x) := F.finite_toSet.isCompact_biUnion (fun x _ => hK x)
  apply hbig.of_isClosed_subset (isClosed_le tangent_norm_continuous continuous_const)
  intro p hp
  obtain ⟨x,hx,hpx⟩ := mem_iUnion₂.mp (hF (mem_univ p.1))
  exact mem_iUnion₂.mpr ⟨x,hx,hbound x p hpx hp⟩

 theorem totalMinimizingSet_compact : IsCompact (totalMinimizingSet (n := n) (M := M)) := by
  apply (tangent_disk_compact (n := n) (M := M) (Metric.diam (univ : Set M))).of_isClosed_subset totalMinimizingSet_closed
  intro p hp
  change ‖p.2‖ ≤ Metric.diam (univ : Set M)
  rw [← show dist p.1 (exp p.1 p.2) = ‖p.2‖ from hp]
  exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
