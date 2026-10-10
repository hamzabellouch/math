import Mathlib
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Holomorphic Common Zeros. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent

def LocallyHolomorphicCommonZeros (X : ComplexManifold.{u}) (Z : Set X.Carrier) : Prop :=
  ∀x,∃U : Set X.Carrier,IsOpen U ∧ x∈U ∧ ∃𝒜 : Set (X.Carrier → ℂ),
    (∀f∈𝒜,ContMDiffOn (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f U) ∧
    ∀y∈U,y∈Z ↔ ∀f∈𝒜,f y=0

lemma LocallyHolomorphicCommonZeros.isClosed {X : ComplexManifold.{u}} {Z : Set X.Carrier}
    (h : LocallyHolomorphicCommonZeros X Z) : IsClosed Z := by
  rw [←isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨U,hU,hxU,𝒜,hf,he⟩ := h x
  have hn : ¬∀f∈𝒜,f x=0 := fun hz => hx ((he x hxU).mpr hz)
  push Not at hn
  obtain ⟨f,hfA,hfx⟩ := hn
  have hn' := ((hf f hfA).contMDiffAt (hU.mem_nhds hxU)).continuousAt.eventually_ne hfx
  filter_upwards [hn',hU.mem_nhds hxU] with y hy hyU
  exact fun hz => hy ((he y hyU).mp hz f hfA)

namespace LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} (L : LeafJetAtlas S)

include L in
lemma commonZeros_closure_interior {Z : Set X.Carrier}
    (hZ : LocallyHolomorphicCommonZeros X Z) : closure (interior Z) ⊆ interior Z := by
  intro x hx
  obtain ⟨U,hU,hxU,𝒜,hf,he⟩ := hZ x
  let P := L.chart x
  let a := P.chart x
  have hxs : x∈P.chart.source := L.mem_source x
  have hat : a∈P.chart.target := P.chart.map_source hxs
  have hUx : P.chart.symm ⁻¹' U∈𝓝 a := by
    apply (P.chart.symm.continuousAt hat).preimage_mem_nhds
    simpa only [a,P.chart.left_inv hxs] using hU.mem_nhds hxU
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (P.chart.open_target.mem_nhds hat) hUx)
  have hN : ∀ᶠy in 𝓝 x,y∈P.chart.source ∧ P.chart y∈Metric.ball a r :=
    Filter.Eventually.and (P.chart.open_source.mem_nhds hxs)
      ((P.chart.continuousAt hxs).preimage_mem_nhds (Metric.ball_mem_nhds a hr))
  obtain ⟨y,hy,hys,hyr⟩ := ((mem_closure_iff_frequently.mp hx).and_eventually hN).exists
  have haF (f : X.Carrier → ℂ) (hfA : f∈𝒜) :
      AnalyticOnNhd ℂ (f ∘ P.chart.symm) (Metric.ball a r) := by
    intro b hb
    exact (((hf f hfA).contMDiffAt (hU.mem_nhds (hrsub hb).2)).comp b
      (P.inverse_holomorphicAt (hrsub hb).1)).contDiffAt.analyticAt
  have hzF (f : X.Carrier → ℂ) (hfA : f∈𝒜) :
      (f ∘ P.chart.symm) =ᶠ[𝓝 (P.chart y)] 0 := by
    have hc := P.chart.symm.continuousAt (P.chart.map_source hys)
    have hzN : P.chart.symm ⁻¹' interior Z∈𝓝 (P.chart y) := by
      apply hc.preimage_mem_nhds
      simpa only [P.chart.left_inv hys] using isOpen_interior.mem_nhds hy
    filter_upwards [hzN,Metric.isOpen_ball.mem_nhds hyr] with b hb hbr
    exact (he _ (hrsub hbr).2).mp (interior_subset hb) f hfA
  have hall (f : X.Carrier → ℂ) (hfA : f∈𝒜) :=
    (haF f hfA).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball a r).isPreconnected hyr (hzF f hfA)
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [hN] with z hzs
  have heq := P.chart.left_inv hzs.1
  have hzU : z∈U := by
    have hh := (hrsub hzs.2).2
    change P.chart.symm (P.chart z)∈U at hh
    rwa [heq] at hh
  apply (he z hzU).mpr
  intro f hfA
  have hz := hall f hfA hzs.2
  simpa only [Function.comp_apply,heq,Pi.zero_apply] using hz

include L in
lemma commonZeros_eq_univ [PreconnectedSpace X.Carrier] {Z : Set X.Carrier}
    (hZ : LocallyHolomorphicCommonZeros X Z) (h : (interior Z).Nonempty) : Z=univ := by
  have hc : IsClosed (interior Z) := isClosed_of_closure_subset
    (L.commonZeros_closure_interior hZ)
  have he : interior Z=univ := (show IsClopen (interior Z) from ⟨hc,isOpen_interior⟩).eq_univ h
  exact eq_univ_of_univ_subset (he ▸ interior_subset)

end LeafJetAtlas
end SplitTangent

end

end OAI
