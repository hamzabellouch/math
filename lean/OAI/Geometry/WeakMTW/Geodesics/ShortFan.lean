import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.FanCoordinates
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

 theorem flowCoordinates_fan (x : M) (P : ℝ → TangentBundle (model n) M)
    {t s : ℝ} (ht : (t,s) ∈ fanDomain x P) (u : ℝ) :
    flowCoordinates x u (fanCoordinates x P (t,s)) = fanCoordinates x P (u+t,s) := by
  change geodesicFlow t (P s) ∈ (stateChart x).source at ht
  dsimp only [flowCoordinates,fanCoordinates,geodesicFan]
  rw [(stateChart x).left_inv ht,← geodesicFlow_add]

 theorem short_fan_bridge (x : M) {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P)
    (h₀ : (1,0) ∈ fanDomain x P) {k : ℝ} (hk : 0 < k) :
    ∃ ε : ℝ, 0 < ε ∧ ε < k ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), (1-ε,s) ∈ fanDomain x P ∧ (1,s) ∈ fanDomain x P ∧
        ShortChartAction x ε (fanCoordinates x P (1-ε,s))) ∧
      ShortChartAction x ε (fanCoordinates x P (1,0)) := by
  let q₀ := fanCoordinates x P (1,0)
  have hz : geodesic (P 0) 1 ∈ (chartAt (Model n) x).source :=
    (stateChart_source x _).mp h₀
  have hshort : ∀ᶠ tq : ℝ × (Model n × Model n) in 𝓝 (0,q₀),
      ShortChartAction x tq.1 tq.2 :=
    eventually_short_chart_action x (geodesic (P 0) 1) hz q₀.2
  obtain ⟨U,hU,hUo,hU₀⟩ := mem_nhds_iff.mp hshort
  have hfc : ContinuousAt (fanCoordinates x P) (1,0) :=
    ((fanCoordinates_smooth x hP _ h₀).contDiffAt ((fanDomain_open x hP).mem_nhds h₀)).continuousAt
  have hj : Continuous (fun ε : ℝ => (1-ε,(0 : ℝ))) :=
    (continuous_const.sub continuous_id).prodMk continuous_const
  have hq : ContinuousAt (fun ε : ℝ => (ε,fanCoordinates x P (1-ε,0))) 0 := by
    have hfc0 : ContinuousAt (fanCoordinates x P) ((fun ε : ℝ => (1-ε,(0 : ℝ))) 0) := by
      simpa only [sub_zero] using hfc
    exact continuousAt_id.prodMk (hfc0.comp (f := fun ε : ℝ => (1-ε,(0 : ℝ))) hj.continuousAt)
  have hr : ContinuousAt (fun ε : ℝ => (ε,q₀)) 0 := continuousAt_id.prodMk continuousAt_const
  have hu : ∀ᶠ ε : ℝ in 𝓝 0,
      (ε,fanCoordinates x P (1-ε,0)) ∈ U ∧ (ε,q₀) ∈ U ∧ (1-ε,0) ∈ fanDomain x P := by
    have hu₁ := hq.preimage_mem_nhds (by simpa only [sub_zero] using hUo.mem_nhds hU₀)
    have hu₂ := hr.preimage_mem_nhds (hUo.mem_nhds hU₀)
    have hd := (hj.continuousAt (x := 0)).preimage_mem_nhds
      (show fanDomain x P ∈ 𝓝 (1-(0 : ℝ),0) by simpa only [sub_zero] using (fanDomain_open x hP).mem_nhds h₀)
    exact inter_mem hu₁ (inter_mem hu₂ hd)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨ε,hε,hεk⟩ := exists_between (lt_min hδ hk)
  have hεp : 0 < ε := hε
  have hεδ : ε < δ := lt_of_lt_of_le hεk (min_le_left _ _)
  have hεk' : ε < k := lt_of_lt_of_le hεk (min_le_right _ _)
  have hh := hball (show ε ∈ Metric.ball (0 : ℝ) δ by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hεp] using hεδ)
  have hd : ContinuousAt (fun s : ℝ => (1-ε,s)) 0 := continuousAt_const.prodMk continuousAt_id
  have hd₁ : ∀ᶠ s in 𝓝 (0 : ℝ), (1-ε,s) ∈ fanDomain x P :=
    hd.preimage_mem_nhds ((fanDomain_open x hP).mem_nhds hh.2.2)
  have hd₂ : ∀ᶠ s in 𝓝 (0 : ℝ), (1,s) ∈ fanDomain x P :=
    (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds ((fanDomain_open x hP).mem_nhds h₀)
  have hfc' := ((fanCoordinates_smooth x hP _ hh.2.2).contDiffAt
    ((fanDomain_open x hP).mem_nhds hh.2.2)).continuousAt
  have hus : ∀ᶠ s in 𝓝 (0 : ℝ), (ε,fanCoordinates x P (1-ε,s)) ∈ U :=
    (continuousAt_const.prodMk (hfc'.comp hd)).preimage_mem_nhds (hUo.mem_nhds hh.1)
  refine ⟨ε,hεp,hεk',?_,hU hh.2.1⟩
  filter_upwards [hd₁,hd₂,hus] with s ha hb hu
  exact ⟨ha,hb,hU hu⟩

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
