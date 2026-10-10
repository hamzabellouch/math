import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.LeafPlaques
import OAI.Geometry.SplitTangent.AllCompactLeaves
import OAI.Geometry.SplitTangent.SwappedProductChart

namespace OAI

/-! Complementary Leaf Intersections. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  (L : LeafJetAtlas S)
  {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

lemma singlePlaque_transverse_eventually (P : AlignedProductChart S A B)
    {Z : Set X.Carrier} {z : X.Carrier} (hzP : z∈P.chart.source)
    (h : L.plaques.LocallySinglePlaque Z z) :
    ∀ᶠ w in 𝓝 z,w∈Z → (P.chart w).2=(P.chart z).2 := by
  obtain ⟨i,U,V,hU,_,hV,_,hzQ,hzUV,huniq⟩ := h
  let Q := L.chart i
  have hc : ContinuousAt Q.chart z := Q.chart.continuousAt hzQ
  have hprod := hc.eventually (Q.transition_product P (Q.chart.map_source hzQ)
    (by simpa only [Q.chart.left_inv hzQ] using hzP))
  have hUV := hc.preimage_mem_nhds ((hU.prod hV).mem_nhds hzUV)
  filter_upwards [Q.chart.open_source.mem_nhds hzQ,hUV,hprod] with w hwQ hwUV hwp hwZ
  have he := huniq w hwZ hwQ hwUV
  have he' : (Q.chart w).2=(Q.chart z).2 := he
  have hs := congrArg Prod.snd hwp
  simp only [Function.comp_apply] at hs
  rw [Q.chart.left_inv hwQ,he',Prod.mk.eta,Q.chart.left_inv hzQ] at hs
  exact hs

variable [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (M : LeafJetAtlas S.swap) (e : ProjectiveEmbedding X)
  (hRC : RationallyConnected e) (hdim : 0<X.dim)

include e hRC hdim in
lemma complementary_leaves_isDiscrete (x y : X.Carrier) :
    IsDiscrete (L.leaf x ∩ M.leaf y) := by
  apply IsDiscrete.of_nhdsWithin
  intro z hz
  let P := L.chart z
  have hzP := L.mem_source z
  have h₁ := L.singlePlaque_transverse_eventually P hzP
    (L.all_leaf_locallySinglePlaque e hRC hdim x z hz.1)
  have h₂ := M.singlePlaque_transverse_eventually P.swap (by simpa using hzP)
    (M.all_leaf_locallySinglePlaque e hRC hdim y z hz.2)
  have hP : ∀ᶠ w in 𝓝 z,w∈P.chart.source := P.chart.open_source.mem_nhds hzP
  apply le_pure_iff.mpr
  filter_upwards [h₁.filter_mono nhdsWithin_le_nhds,h₂.filter_mono nhdsWithin_le_nhds,
    hP.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
    with w hw₁ hw₂ hwP hw
  apply P.chart.injOn hwP hzP
  exact Prod.ext (hw₂ hw.2) (hw₁ hw.1)

include e hRC hdim in
lemma complementary_leaves_finite (x y : X.Carrier) : (L.leaf x ∩ M.leaf y).Finite :=
  ((L.all_leaf_isCompact e hRC hdim x).inter_right
    (M.all_leaf_isClosed e hRC hdim y)).finite
      (L.complementary_leaves_isDiscrete M e hRC hdim x y)

end SplitTangent.LeafJetAtlas

end

end OAI
