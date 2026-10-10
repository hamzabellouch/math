import Mathlib
import OAI.Geometry.WeakMTW.Potentials.PotentialGraphGlobal

namespace OAI

namespace WeakMTWGlobalSupport

section

open Manifold Bundle
open scoped Topology ContDiff Manifold

theorem current_global_support
    {n : ℕ} (_hn : 2 ≤ n) {M : Type*}
    [MetricSpace M] [ChartedSpace (WeakMTW.Model n) M]
    [IsManifold (WeakMTW.model n) ∞ M]
    [CompactSpace M] [ConnectedSpace M]
    [RiemannianBundle (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsContMDiffRiemannianBundle (WeakMTW.model n) ∞ (WeakMTW.Model n)
      (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsRiemannianManifold (WeakMTW.model n) M]
    (hmtw : WeakMTW.HasWeakMTW (n := n) (M := M))
    (u : M → ℝ) (hu : WeakMTW.IsPotential u) :
    WeakMTW.GlobalSupportingProperty (n := n) u := WeakMTW.globalSupportingProperty hmtw hu
end

end WeakMTWGlobalSupport

end OAI
