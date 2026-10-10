import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.AllCompactLeaves

namespace OAI

/-! Transverse Discrete. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} (L : LeafJetAtlas S)
  {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

omit [CompleteSpace A] [CompleteSpace B]
lemma transverse_isolated (P : AlignedProductChart S A B)
    {Z : Set X.Carrier} {a : A} {b : B} (ht : (a,b)∈P.chart.target)
    (h : L.plaques.LocallySinglePlaque Z (P.chart.symm (a,b))) :
    ∀ᶠ c in 𝓝 b,P.chart.symm (a,c)∈Z → c=b := by
  obtain ⟨i,U,V,hU,_,hV,_,hys,hyUV,huniq⟩ := h
  let Q := L.chart i
  let f : B → X.Carrier := fun c => P.chart.symm (a,c)
  have hp : Tendsto (fun c : B => (a,c)) (𝓝 b) (𝓝 (a,b)) :=
    continuousAt_const.prodMk continuousAt_id
  have hf : ContinuousAt f b := (P.chart.symm.continuousAt ht).comp hp
  have hQ : ∀ᶠ c in 𝓝 b,f c∈Q.chart.source :=
    hf.preimage_mem_nhds (Q.chart.open_source.mem_nhds hys)
  have hUV : ∀ᶠ c in 𝓝 b,Q.chart (f c)∈U ×ˢ V :=
    (ContinuousAt.comp (f := f) (g := Q.chart) (Q.chart.continuousAt hys) hf).preimage_mem_nhds ((hU.prod hV).mem_nhds hyUV)
  have hT : ∀ᶠ c in 𝓝 b,(a,c)∈P.chart.target :=
    hp.eventually (P.chart.open_target.mem_nhds ht)
  have hprod := hp.eventually (P.transition_product Q ht hys)
  filter_upwards [hQ,hUV,hT,hprod] with c hc hcUV hct hpc hcz
  have hs : (Q.chart (f c)).2=(Q.chart (f b)).2 := huniq _ hcz hc hcUV
  have hfst : (Q.chart (f c)).1=(Q.chart (f b)).1 := by
    simpa only [Function.comp_apply,f] using
      congrArg (fun p : S.FirstModel i × S.SecondModel i => p.1) hpc
  have he : f c=f b := Q.chart.injOn hc hys (Prod.ext hfst hs)
  have he' := congrArg (fun y => (P.chart y).2) he
  simpa only [f,P.chart.right_inv ht,P.chart.right_inv hct] using he'

lemma transverse_leaf_isDiscrete [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
    (e : ProjectiveEmbedding X) (hRC : RationallyConnected e) (hdim : 0<X.dim)
    (P : AlignedProductChart S A B) (x : X.Carrier) (a : A) :
    IsDiscrete {b : B | (a,b)∈P.chart.target ∧ P.chart.symm (a,b)∈L.leaf x} := by
  apply IsDiscrete.of_nhdsWithin
  intro b hb
  apply le_pure_iff.mpr
  have hh := L.transverse_isolated P hb.1
    (L.all_leaf_locallySinglePlaque e hRC hdim x _ hb.2)
  filter_upwards [hh.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with c hc hcZ
  exact hc hcZ.2

lemma finite_compact_transversal [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
    (e : ProjectiveEmbedding X) (hRC : RationallyConnected e) (hdim : 0<X.dim)
    (P : AlignedProductChart S A B) (x : X.Carrier) (a : A)
    {K : Set B} (hK : IsCompact K) (hT : ∀b∈K,(a,b)∈P.chart.target) :
    {b∈K | P.chart.symm (a,b)∈L.leaf x}.Finite := by
  have hf : ContinuousOn (fun b => P.chart.symm (a,b)) K := by
    intro b hb
    exact ((P.chart.symm.continuousAt (hT b hb)).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hs : Continuous (fun b : K => P.chart.symm (a,b.val)) :=
    continuousOn_iff_continuous_domRestrict.mp hf
  have hC : IsCompact {b : K | P.chart.symm (a,b.val)∈L.leaf x} :=
    ((L.all_leaf_isClosed e hRC hdim x).preimage hs).isCompact
  have hc : IsCompact {b∈K | P.chart.symm (a,b)∈L.leaf x} := by
    convert hC.image continuous_subtype_val using 1
    ext b
    constructor
    · intro hb
      exact ⟨⟨b,hb.1⟩,hb.2,rfl⟩
    · rintro ⟨c,hc,rfl⟩
      exact ⟨c.property,hc⟩
  exact hc.finite ((L.transverse_leaf_isDiscrete e hRC hdim P x a).mono
    (fun b hb => ⟨hT b hb.1,hb.2⟩))

end SplitTangent.LeafJetAtlas

end

end OAI
