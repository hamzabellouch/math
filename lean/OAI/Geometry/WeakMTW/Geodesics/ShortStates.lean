import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.GlobalFlow
import OAI.Geometry.WeakMTW.Geodesics.ShortChartAction

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

 theorem short_state_bridge (y : M) (p : TangentBundle (model n) M)
    (hp : geodesicFlow 1 p ∈ (stateChart y).source) {k : ℝ} (hk : 0 < k) :
    ∃ ε : ℝ, 0 < ε ∧ ε < k ∧
      ∀ᶠ p' : TangentBundle (model n) M in 𝓝 p,
        geodesicFlow (1-ε) p' ∈ (stateChart y).source ∧
        geodesicFlow 1 p' ∈ (stateChart y).source ∧
        ShortChartAction y ε (stateChart y (geodesicFlow (1-ε) p')) := by
  let d := stateChart (E := Model n) y
  let q₀ := d (geodesicFlow 1 p)
  have hz : geodesic p 1 ∈ (chartAt (Model n) y).source := (stateChart_source y _).mp hp
  have hs := eventually_short_chart_action y (geodesic p 1) hz q₀.2
  have hs' : ∀ᶠ tq : ℝ × (Model n × Model n) in 𝓝 (0,q₀), ShortChartAction y tq.1 tq.2 := hs
  obtain ⟨U,hU,hUo,hU₀⟩ := mem_nhds_iff.mp hs'
  have hflow : ContinuousAt (fun ε : ℝ => geodesicFlow (1-ε) p) 0 := by
    exact (geodesicFlow_smooth (n := n) (M := M)).continuous.continuousAt.comp
      ((continuousAt_const.sub continuousAt_id).prodMk continuousAt_const)
  have hq : ContinuousAt (fun ε : ℝ => (ε,d (geodesicFlow (1-ε) p))) 0 := by
    refine continuousAt_id.prodMk ?_
    exact (d.continuousAt (by simpa only [sub_zero] using hp)).comp hflow
  have hnear : ∀ᶠ ε : ℝ in 𝓝 0,
      (ε,d (geodesicFlow (1-ε) p)) ∈ U ∧ geodesicFlow (1-ε) p ∈ d.source := by
    refine inter_mem (hq.preimage_mem_nhds ?_) (hflow.preimage_mem_nhds ?_)
    · simpa only [sub_zero] using hUo.mem_nhds hU₀
    · rw [sub_zero]
      exact d.open_source.mem_nhds hp
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨ε,hε,hεk⟩ := exists_between (lt_min hδ hk)
  have hεδ : ε < δ := lt_of_lt_of_le hεk (min_le_left _ _)
  have hεk' : ε < k := lt_of_lt_of_le hεk (min_le_right _ _)
  have hh := hball (show ε ∈ Metric.ball (0 : ℝ) δ by
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hε] using hεδ)
  have hF : ContinuousAt (geodesicFlow (1-ε) : TangentBundle (model n) M → TangentBundle (model n) M) p :=
    (geodesicFlow_smooth_fixed (1-ε)).continuous.continuousAt
  have hC := (d.continuousAt hh.2).comp hF
  have hU' : ∀ᶠ p' : TangentBundle (model n) M in 𝓝 p,
      (ε,d (geodesicFlow (1-ε) p')) ∈ U :=
    (continuousAt_const.prodMk hC).preimage_mem_nhds (hUo.mem_nhds hh.1)
  have hτ' := hF.preimage_mem_nhds (d.open_source.mem_nhds hh.2)
  have h₁' := (geodesicFlow_smooth_fixed (n := n) (M := M) 1).continuous.continuousAt.preimage_mem_nhds
    (d.open_source.mem_nhds hp)
  refine ⟨ε,hε,hεk',?_⟩
  filter_upwards [hU',hτ',h₁'] with p' hpU hpτ hp₁
  exact ⟨hpτ,hp₁,hU hpU⟩

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
