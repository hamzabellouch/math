import Mathlib
import OAI.Geometry.SplitTangent.FoliationLeaves

namespace OAI

/-! Plaque Connected Sets. -/

noncomputable section
open Set Filter Topology
universe u v w
namespace PlaqueSystem
variable {ι : Type v} {X : Type u} [TopologicalSpace X]
  {A B : ι → Type w} [∀i,TopologicalSpace (A i)] [∀i,TopologicalSpace (B i)]
  (P : PlaqueSystem X A B)

lemma LocallySinglePlaque.eventually_reachable {Z : Set X} {z : X}
    (h : P.LocallySinglePlaque Z z) : ∀ᶠ y in 𝓝[Z] z,P.Reachable z y := by
  obtain ⟨i,U,V,hU,hUc,hV,hT,hzs,hzUV,huniq⟩ := h
  have hn : ∀ᶠ y in 𝓝 z,y∈(P.chart i).source ∧ (P.chart i) y∈U ×ˢ V :=
    Filter.Eventually.and ((P.chart i).open_source.mem_nhds hzs)
      (((P.chart i).continuousAt hzs).preimage_mem_nhds ((hU.prod hV).mem_nhds hzUV))
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with y hy hyZ
  have he := huniq y hyZ hy.1 hy.2
  have hr := P.related_in_rectangle hUc hT hzUV.1 hy.2.1 hzUV.2
  have hy' : (P.chart i).symm (((P.chart i) y).1,((P.chart i) z).2)=y := by
    rw [←he]
    exact (P.chart i).left_inv hy.1
  change P.Related ((P.chart i).symm ((P.chart i) z))
    ((P.chart i).symm (((P.chart i) y).1,((P.chart i) z).2)) at hr
  rw [(P.chart i).left_inv hzs,hy'] at hr
  exact Relation.ReflTransGen.single hr

 

lemma preconnected_subset_leaf {Z : Set X} (hZ : IsPreconnected Z)
    (hlocal : ∀z∈Z,P.LocallySinglePlaque Z z) {x : X} (hx : x∈Z) : Z⊆P.leaf x := by
  let : PreconnectedSpace Z := isPreconnected_iff_preconnectedSpace.mp hZ
  let f : Z → Prop := fun y => P.Reachable x y.val
  have hf : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_eventually_eq f).mpr
    intro y
    have ht : Tendsto (Subtype.val : Z → X) (𝓝 y) (𝓝[Z] y.val) :=
      tendsto_inf.mpr ⟨continuous_subtype_val.tendsto y,
        tendsto_principal.mpr (Filter.Eventually.of_forall (fun z : Z => z.property))⟩
    have hh := ht.eventually
      ((hlocal y.val y.property).eventually_reachable P)
    filter_upwards [hh] with z hz
    apply propext
    exact ⟨fun hxz => Reachable.trans P hxz (Reachable.symm P hz),fun hxy => Reachable.trans P hxy hz⟩
  intro y hy
  have hh := hf.apply_eq_of_preconnectedSpace (⟨y,hy⟩ : Z) ⟨x,hx⟩
  exact hh.mpr (Reachable.refl P x)

end PlaqueSystem

end

end OAI
