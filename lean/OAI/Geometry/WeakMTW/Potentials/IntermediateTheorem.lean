import Mathlib
import OAI.Geometry.WeakMTW.Potentials.IntermediateGrowth
import OAI.Geometry.WeakMTW.Potentials.IntermediateStatement

namespace OAI

namespace WeakMTWGlobalSupport

section

open Manifold Bundle
open scoped Topology ContDiff Manifold

theorem current_intermediate_geometry
    {n : ℕ} (_hn : 2 ≤ n) {M : Type*}
    [MetricSpace M] [ChartedSpace (WeakMTW.Model n) M]
    [IsManifold (WeakMTW.model n) ∞ M]
    [CompactSpace M] [ConnectedSpace M]
    [RiemannianBundle (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsContMDiffRiemannianBundle (WeakMTW.model n) ∞ (WeakMTW.Model n)
      (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsRiemannianManifold (WeakMTW.model n) M]
    (hmtw : WeakMTW.HasWeakMTW (n := n) (M := M)) :
    WeakMTW.IntermediateGeometry hmtw
 := by
  refine ⟨?_, WeakMTW.intermediate_uniform_c11 hmtw,
    WeakMTW.intermediate_uniform_lipschitz hmtw, WeakMTW.intermediate_uniform_growth hmtw⟩
  intro u v huv t ht ht1
  refine ⟨WeakMTW.hopfLax_duality hmtw huv ht ht1,
    WeakMTW.intermediate_c11 hmtw huv ht ht1, ?_⟩
  intro z
  have hflow := WeakMTW.intermediate_pole_flow hmtw huv ht ht1 z
  refine ⟨hflow, ?_⟩
  change (WeakMTW.intermediateInverse hmtw ⟨v,huv.2.1,huv.2.2.1⟩ ht ht1 z).1 = _
  have hb := congrArg (fun q : TangentBundle (WeakMTW.model n) M => q.1) hflow
  exact hb.trans (WeakMTW.exp_mul_eq_geodesic
    (⟨z,WeakMTW.normalGradient (WeakMTW.hopfLax t u) z⟩ : TangentBundle (WeakMTW.model n) M) (-t)).symm
end

end WeakMTWGlobalSupport

end OAI
