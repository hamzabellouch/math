import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.NormalState
import OAI.Geometry.WeakMTW.Geodesics.GeodesicScaling
import OAI.Geometry.WeakMTW.Coordinates.ChartScaling

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def flowCoordinates (x : M) (t : ℝ) (q : Model n × Model n) : Model n × Model n :=
   stateChart x (geodesicFlow t ((stateChart x).symm q))

 theorem normal_flow_rescaled (x : M) {y₀ : Model n}
    (N : NormalFlow (metric x) (chartAt (Model n) x).target y₀)
    {q : Model n × Model n} (hq : q ∈ (stateChart x).target) (a : ℝ)
    (hr : (q.1,a•q.2) ∈ N.normal.source) :
    geodesicFlow (a*N.time) ((stateChart x).symm q) ∈ (stateChart x).source ∧
    N.flow (N.time,(q.1,a•q.2)) =
      ((flowCoordinates x (a*N.time) q).1,a • (flowCoordinates x (a*N.time) q).2) := by
  have hh := geodesicFlow_normal x N hr ⟨N.time_pos.le,le_rfl⟩
  rw [stateChart_symm_mul x a hq,geodesicFlow_mulState] at hh
  have hm : N.flow (N.time,(q.1,a•q.2)) ∈ (stateChart x).target :=
    (stateChart_target x _).mpr (N.ode _ (N.source_stays _ hr _ ⟨N.time_pos.le,le_rfl⟩)).1
  have hF : geodesicFlow (a*N.time) ((stateChart x).symm q) ∈ (stateChart x).source := by
    have hmul := hh.symm ▸ (stateChart x).map_target hm
    exact (stateChart_source x _).mpr ((stateChart_source x _).mp hmul)
  refine ⟨hF,?_⟩
  have he := congrArg (stateChart x) hh
  rw [stateChart_mulState x a _ hF,(stateChart x).right_inv hm] at he
  exact he.symm

 theorem normal_endpoint_rescaled (x : M) {y₀ : Model n}
    (N : NormalFlow (metric x) (chartAt (Model n) x).target y₀)
    {q : Model n × Model n} (hq : q ∈ (stateChart x).target) (a : ℝ)
    (hr : (q.1,a•q.2) ∈ N.normal.source) :
    N.normal (q.1,a•q.2) = (q.1,(flowCoordinates x (a*N.time) q).1) := by
  rw [N.normal_apply,(normal_flow_rescaled x N hq a hr).2]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
