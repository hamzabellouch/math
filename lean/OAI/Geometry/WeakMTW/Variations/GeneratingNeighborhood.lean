import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.ShortStates
import OAI.Geometry.WeakMTW.Variations.GeneratingActionBound

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def GeneratingChartAction (x y : M) (ε : ℝ) (q : Model n × Model n) : Prop :=
    q ∈ (stateChart x).target ∧
    geodesicFlow (1-ε) ((stateChart x).symm q) ∈ (stateChart y).source ∧
    geodesicFlow 1 ((stateChart x).symm q) ∈ (stateChart y).source ∧
    ShortChartAction y ε (crossFlowCoordinates x y (1-ε) q)

 theorem exists_generating_neighborhood (x y : M) {q : Model n × Model n}
    (hq : q ∈ (stateChart x).target)
    (hy : geodesicFlow 1 ((stateChart x).symm q) ∈ (stateChart y).source) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ r in 𝓝 q, GeneratingChartAction x y ε r := by
  obtain ⟨ε,hε,hε₁,hev⟩ := short_state_bridge y ((stateChart x).symm q) hy (k := 1) zero_lt_one
  have hc : ContinuousAt ((stateChart (E := Model n) x).symm) q := (stateChart x).symm.continuousAt hq
  refine ⟨ε,hε,hε₁,?_⟩
  filter_upwards [(stateChart x).open_target.mem_nhds hq,hc.tendsto hev] with r hr hh
  exact ⟨hr,hh.1,hh.2.1,hh.2.2⟩

 theorem GeneratingChartAction.smooth {x y : M} {ε : ℝ} {q : Model n × Model n}
    (h : GeneratingChartAction x y ε q) :
    ContDiffAt ℝ ∞ (generatingAction x y ε) (q,(crossFlowCoordinates x y 1 q).1) :=
    generatingAction_smooth x y h.1 h.2.1 h.2.2.2

 theorem GeneratingChartAction.flow_smooth {x y : M} {ε : ℝ} {q : Model n × Model n}
    (h : GeneratingChartAction x y ε q) : ContDiffAt ℝ ∞ (crossFlowCoordinates x y 1) q :=
    chart_flow_smooth x y 1 h.1 h.2.2.1

 theorem generating_vertical_minimum (x y : M) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    {q : Model n × Model n} (hq : GeneratingChartAction x y ε q)
    (hm : dist ((stateChart x).symm q).1 (geodesic ((stateChart x).symm q) 1) = ‖((stateChart x).symm q).2‖) :
    IsLocalMin (fun ν : Model n => generatingAction x y ε ((q.1,ν),(crossFlowCoordinates x y 1 q).1)) q.2 := by
  have hc : ContinuousAt (fun ν : Model n => (q.1,ν)) q.2 := continuousAt_const.prodMk continuousAt_id
  have hqnear : ∀ᶠ r in 𝓝 q, r ∈ (stateChart x).target ∧
      geodesicFlow (1-ε) ((stateChart x).symm r) ∈ (stateChart y).source := by
    refine inter_mem ((stateChart x).open_target.mem_nhds hq.1) ?_
    exact ((geodesicFlow_smooth_fixed (1-ε)).continuous.continuousAt.comp
      ((stateChart x).symm.continuousAt hq.1)).preimage_mem_nhds
        ((stateChart y).open_source.mem_nhds hq.2.1)
  have hmin := generatingAction_eq_minimizing x y hε hε₁ hq.1 hq.2.1 hq.2.2.1 hm
  filter_upwards [hc.tendsto hqnear] with ν hν
  change generatingAction x y ε (q,(crossFlowCoordinates x y 1 q).1) ≤ _
  rw [hmin]
  exact generatingAction_bound x y hε hε₁ hν.1 hν.2 _

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
