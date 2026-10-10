import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.LocalCost
import OAI.Geometry.WeakMTW.Coordinates.EndpointAction

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
  [IsRiemannianManifold (model n) M]

 def chartCost (x : M) (q : Model n × Model n) : ℝ :=
   cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) x).symm q.2)

 theorem chartCost_eq_endpointAction (x z : M) (hz : z ∈ (chartAt (Model n) x).source)
    (N : NormalFlow (metric x) (chartAt (Model n) x).target (chartAt (Model n) x z)) :
    chartCost x =ᶠ[𝓝 (chartAt (Model n) x z,chartAt (Model n) x z)] N.endpointAction := by
  have he := N.normal_zero (chartAt (Model n) x).open_target (metric_smooth x)
    (fun y hy v hv => metric_positive x hy hv) N.center_mem
  have ht : (chartAt (Model n) x z,chartAt (Model n) x z) ∈ N.normal.target :=
    he ▸ N.normal.map_source N.center_mem
  filter_upwards [cost_coord_eq_normal x z hz N,N.normal.open_target.mem_nhds ht] with q hq hqt
  change _ = N.time^2/2 * metric x (N.normal.symm q).1 (N.normal.symm q).2 (N.normal.symm q).2
  rw [N.inverse_fst hqt]
  exact hq

 theorem eventually_chartCost_derivative (x z : M) (hz : z ∈ (chartAt (Model n) x).source)
    (N : NormalFlow (metric x) (chartAt (Model n) x).target (chartAt (Model n) x z)) :
    ∀ᶠ q : Model n × Model n in 𝓝 (chartAt (Model n) x z,chartAt (Model n) x z),
      q ∈ N.normal.target ∧ ContDiffAt ℝ ∞ (chartCost x) q ∧
        ∀ w, fderiv ℝ (chartCost x) q w = N.time *
          (metric x (N.flow (N.time,N.normal.symm q)).1 (N.flow (N.time,N.normal.symm q)).2 w.2 -
            metric x q.1 (N.normal.symm q).2 w.1) := by
  have he := N.normal_zero (chartAt (Model n) x).open_target (metric_smooth x)
    (fun y hy v hv => metric_positive x hy hv) N.center_mem
  have ht : (chartAt (Model n) x z,chartAt (Model n) x z) ∈ N.normal.target :=
    he ▸ N.normal.map_source N.center_mem
  filter_upwards [(chartCost_eq_endpointAction x z hz N).eventuallyEq_nhds,
    N.normal.open_target.mem_nhds ht] with q hq hqt
  refine ⟨hqt,?_,?_⟩
  · exact (((N.endpointAction_smooth (chartAt (Model n) x).open_target (metric_smooth x) _ hqt).contDiffAt
      (N.normal.open_target.mem_nhds hqt)).congr_of_eventuallyEq hq)
  · intro w
    rw [hq.fderiv_eq]
    exact N.endpointAction_derivative (chartAt (Model n) x).open_target (metric_smooth x)
      (fun y _ => metric_symmetric x y) (fun y hy v hv => metric_positive x hy hv) hqt w

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
