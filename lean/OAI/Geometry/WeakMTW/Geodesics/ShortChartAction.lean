import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.CostEndpointAction
import OAI.Geometry.WeakMTW.Geodesics.ShortFlowCoordinates

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

 def ShortChartAction (x : M) (t : ℝ) (q : Model n × Model n) : Prop :=
   q ∈ (stateChart x).target ∧
   geodesicFlow t ((stateChart x).symm q) ∈ (stateChart x).source ∧
   ContDiffAt ℝ ∞ (chartCost x) (q.1,(flowCoordinates x t q).1) ∧
   ∀ w : Model n × Model n,
     fderiv ℝ (chartCost x) (q.1,(flowCoordinates x t q).1) w = t *
       (metric x (flowCoordinates x t q).1 (flowCoordinates x t q).2 w.2 - metric x q.1 q.2 w.1)

 theorem chartCost_short_of_normal (x z : M) (_hz : z ∈ (chartAt (Model n) x).source)
    (N : NormalFlow (metric x) (chartAt (Model n) x).target (chartAt (Model n) x z))
    {q : Model n × Model n} (hq : q ∈ (stateChart x).target) (a : ℝ)
    (hr : (q.1,a•q.2) ∈ N.normal.source)
    (he : chartCost x =ᶠ[𝓝 (N.normal (q.1,a•q.2))] N.endpointAction) :
    ShortChartAction x (a*N.time) q := by
  have hm := normal_flow_rescaled x N hq a hr
  have hp : N.normal (q.1,a•q.2) = (q.1,(flowCoordinates x (a*N.time) q).1) :=
    normal_endpoint_rescaled x N hq a hr
  have ht := N.normal.map_source hr
  have hs := ((N.endpointAction_smooth (chartAt (Model n) x).open_target (metric_smooth x) _ ht).contDiffAt
    (N.normal.open_target.mem_nhds ht)).congr_of_eventuallyEq he
  refine ⟨hq,hm.1,hp ▸ hs,?_⟩
  intro w
  rw [← hp,he.fderiv_eq,N.endpointAction_derivative (chartAt (Model n) x).open_target
    (metric_smooth x) (fun y _ => metric_symmetric x y)
    (fun y hy v hv => metric_positive x hy hv) ht w,N.normal.left_inv hr,N.normal_apply,hm.2]
  simp only [map_smul,smul_apply,smul_eq_mul]
  ring

 theorem eventually_short_chart_action (x z : M) (hz : z ∈ (chartAt (Model n) x).source)
    (v : Model n) :
    ∀ᶠ tq : ℝ × (Model n × Model n) in 𝓝 (0,(chartAt (Model n) x z,v)),
      ShortChartAction x tq.1 tq.2 := by
  let c := chartAt (Model n) x
  let q₀ : Model n × Model n := (c z,v)
  obtain ⟨N⟩ := exists_normalFlow c.open_target (metric_smooth x)
    (fun y hy v hv => metric_positive x hy hv) (c.map_source hz)
  let r : ℝ × (Model n × Model n) → Model n × Model n := fun tq => (tq.2.1,(tq.1/N.time)•tq.2.2)
  have hr : Continuous r := continuous_snd.fst.prodMk
    ((continuous_fst.div_const N.time).smul continuous_snd.snd)
  have hr₀ : r (0,q₀) = (c z,0) := by simp [r,q₀]
  have hq₀ : q₀ ∈ (stateChart x).target := (stateChart_target x _).mpr (c.map_source hz)
  have hnr : ContinuousAt (fun tq => N.normal (r tq)) (0,q₀) :=
    (N.normal.continuousAt (hr₀ ▸ N.center_mem)).comp hr.continuousAt
  have hn₀ : N.normal (r (0,q₀)) = (c z,c z) := by
    rw [hr₀]
    exact N.normal_zero c.open_target (metric_smooth x)
      (fun y hy v hv => metric_positive x hy hv) N.center_mem
  have hnear : ∀ᶠ tq in 𝓝 (0,q₀), tq.2 ∈ (stateChart x).target ∧ r tq ∈ N.normal.source :=
    inter_mem (continuousAt_snd.preimage_mem_nhds ((stateChart x).open_target.mem_nhds hq₀))
      (hr.continuousAt.preimage_mem_nhds (hr₀ ▸ N.normal.open_source.mem_nhds N.center_mem))
  have he : ∀ᶠ tq in 𝓝 (0,q₀), chartCost x =ᶠ[𝓝 (N.normal (r tq))] N.endpointAction := by
    have hh := (chartCost_eq_endpointAction x z hz N).eventuallyEq_nhds
    rw [← hn₀] at hh
    exact hnr.tendsto hh
  filter_upwards [hnear,he] with tq htq heq
  have hh := chartCost_short_of_normal x z hz N htq.1 (tq.1/N.time) htq.2 heq
  simpa only [div_mul_cancel₀ _ N.time_pos.ne'] using hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
