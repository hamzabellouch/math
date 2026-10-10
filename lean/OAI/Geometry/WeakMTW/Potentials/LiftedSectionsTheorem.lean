import Mathlib
import OAI.Geometry.WeakMTW.Potentials.LiftedSections

namespace OAI

namespace WeakMTWGlobalSupport

section

open Manifold Bundle
open scoped Topology ContDiff Manifold

theorem current_lifted_sections
    {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [MetricSpace M] [ChartedSpace (WeakMTW.Model n) M]
    [IsManifold (WeakMTW.model n) ∞ M]
    [CompactSpace M] [ConnectedSpace M]
    [RiemannianBundle (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsContMDiffRiemannianBundle (WeakMTW.model n) ∞ (WeakMTW.Model n)
      (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsRiemannianManifold (WeakMTW.model n) M]
    (hmtw : WeakMTW.HasWeakMTW (n := n) (M := M))
    (u v : M → ℝ) (huv : WeakMTW.IsDualPair u v) :
    WeakMTW.ConvexLiftedSections (n := n) u v := by
  obtain ⟨dimensionOffset, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact WeakMTW.convexLiftedSections hmtw huv
end

end WeakMTWGlobalSupport

end OAI
