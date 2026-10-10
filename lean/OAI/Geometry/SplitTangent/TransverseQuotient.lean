import Mathlib
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.CompactLeafQuotient
import OAI.Geometry.SplitTangent.TransverseDiscrete

namespace OAI

/-! Transverse Quotient. -/

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (e : ProjectiveEmbedding X)
  (hRC : RationallyConnected e) (hdim : 0<X.dim)
  (i : X.Carrier) {U : Set (S.FirstModel i)} {V : Set (S.SecondModel i)}

lemma leafQuotient_constant_plaque (hUc : IsPreconnected U)
    (hrect : U ×ˢ V ⊆ (L.chart i).chart.target)
    {a a' : S.FirstModel i} {b : S.SecondModel i} (ha : a∈U) (ha' : a'∈U) (hb : b∈V) :
    L.leafQuotient e hRC hdim ((L.chart i).chart.symm (a,b))=
      L.leafQuotient e hRC hdim ((L.chart i).chart.symm (a',b)) := by
  apply (L.leafQuotient_eq_iff e hRC hdim _ _).mpr
  exact Relation.ReflTransGen.single (L.plaques.related_in_rectangle hUc hrect ha ha' hb)

lemma quotient_rectangle_image (hUc : IsPreconnected U)
    (hrect : U ×ˢ V ⊆ (L.chart i).chart.target)
    {a : S.FirstModel i} (ha : a∈U) {W : Set (S.SecondModel i)} (hW : W⊆V) :
    L.leafQuotient e hRC hdim '' ((L.chart i).chart.symm '' (U ×ˢ W))=
      (fun b => L.leafQuotient e hRC hdim ((L.chart i).chart.symm (a,b))) '' W := by
  ext K
  constructor
  · rintro ⟨x,⟨⟨c,b⟩,⟨hc,hb⟩,rfl⟩,rfl⟩
    exact ⟨b,hb,L.leafQuotient_constant_plaque e hRC hdim i hUc hrect ha hc (hW hb)⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨(L.chart i).chart.symm (a,b),⟨(a,b),⟨ha,hb⟩,rfl⟩,rfl⟩

def transverseQuotient (a : S.FirstModel i) (V : Set (S.SecondModel i)) :
    V → L.CompactLeafSpace e hRC hdim :=
  fun b => L.leafQuotient e hRC hdim ((L.chart i).chart.symm (a,b.val))

lemma continuous_transverseQuotient {a : S.FirstModel i}
    (hT : ∀b∈V,(a,b)∈(L.chart i).chart.target) :
    Continuous (L.transverseQuotient e hRC hdim i a V) := by
  have hs : Continuous (fun b : V => (L.chart i).chart.symm (a,b.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro b
    exact ((L.chart i).chart.symm.continuousAt (hT b.val b.property)).comp
      (f := fun b : V => (a,b.val)) (x := b)
      (continuousAt_const.prodMk continuous_subtype_val.continuousAt)
  exact (L.continuous_leafQuotient e hRC hdim).comp hs

lemma isOpenMap_transverseQuotient (hU : IsOpen U) (hUc : IsPreconnected U) (hV : IsOpen V)
    (hrect : U ×ˢ V ⊆ (L.chart i).chart.target) {a : S.FirstModel i} (ha : a∈U) :
    IsOpenMap (L.transverseQuotient e hRC hdim i a V) := by
  intro W hW
  let W' : Set (S.SecondModel i) := Subtype.val '' W
  have hw : IsOpen W' := hV.isOpenMap_subtype_val W hW
  have hwV : W'⊆V := fun b hb => by rcases hb with ⟨c,hc,rfl⟩; exact c.property
  have hopen := L.isOpenMap_leafQuotient e hRC hdim _
    ((L.chart i).chart.symm.isOpen_image_of_subset_source (hU.prod hw)
      (fun p hp => hrect ⟨hp.1,hwV hp.2⟩))
  rw [L.quotient_rectangle_image e hRC hdim i hUc hrect ha hwV] at hopen
  convert hopen using 1
  simp only [W',Set.image_image,transverseQuotient]
  rfl

lemma transverseQuotient_fiber_isDiscrete {a : S.FirstModel i}
    (hT : ∀b∈V,(a,b)∈(L.chart i).chart.target) (K : L.CompactLeafSpace e hRC hdim) :
    IsDiscrete {b : S.SecondModel i | b∈V ∧
      L.leafQuotient e hRC hdim ((L.chart i).chart.symm (a,b))=K} := by
  obtain ⟨x,hx⟩ := L.surjective_leafQuotient e hRC hdim K
  subst K
  apply (L.transverse_leaf_isDiscrete e hRC hdim (L.chart i) x a).mono
  intro b hb
  refine ⟨hT b hb.1,?_⟩
  exact (L.leafQuotient_eq_iff e hRC hdim _ _).mp hb.2.symm

lemma transverseQuotient_fiber_finite {a : S.FirstModel i}
    {K : Set (S.SecondModel i)} (hK : IsCompact K)
    (hT : ∀b∈K,(a,b)∈(L.chart i).chart.target) (q : L.CompactLeafSpace e hRC hdim) :
    {b∈K | L.leafQuotient e hRC hdim ((L.chart i).chart.symm (a,b))=q}.Finite := by
  obtain ⟨x,hx⟩ := L.surjective_leafQuotient e hRC hdim q
  subst q
  convert L.finite_compact_transversal e hRC hdim (L.chart i) x a hK hT using 1
  ext b
  simp only [Set.mem_ofPred_eq]
  exact and_congr_right fun _ =>
    ⟨fun h => (L.leafQuotient_eq_iff e hRC hdim _ _).mp h.symm,
      fun h => ((L.leafQuotient_eq_iff e hRC hdim _ _).mpr h).symm⟩

end SplitTangent.LeafJetAtlas

end

end OAI
