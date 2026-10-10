import Mathlib
import OAI.Geometry.SplitTangent.CompactSetLimits
import OAI.Geometry.SplitTangent.FoliationLeaves
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.LeafPlaques
import OAI.Geometry.SplitTangent.AllCompactLeaves

namespace OAI

/-! Leaf Compact Limits. -/

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (e : ProjectiveEmbedding X)
  (hRC : RationallyConnected e) (hdim : 0<X.dim)

def compactLeaf (x : X.Carrier) : Compacts X.Carrier :=
  ⟨L.leaf x,L.all_leaf_isCompact e hRC hdim x⟩

def leafLimits : Set (Compacts X.Carrier) := closure (range (L.compactLeaf e hRC hdim))

lemma leafLimits_preconnected {K : Compacts X.Carrier} (hK : K∈L.leafLimits e hRC hdim) :
    IsPreconnected (K : Set X.Carrier) := by
  apply (closure_minimal (t := {K : Compacts X.Carrier | IsPreconnected (K : Set X.Carrier)})
    ?_ CompactSetLimits.isClosed_preconnected) hK
  rintro _ ⟨x,rfl⟩
  exact (L.plaques.leaf_isConnected x).2

lemma leafLimits_nonempty {K : Compacts X.Carrier} (hK : K∈L.leafLimits e hRC hdim) :
    (K : Set X.Carrier).Nonempty := by
  apply Compacts.coe_nonempty.mpr
  have hh : K∈({⊥} : Set (Compacts X.Carrier))ᶜ :=
    (closure_minimal (t := ({⊥} : Set (Compacts X.Carrier))ᶜ) (by
      rintro _ ⟨x,rfl⟩
      exact Compacts.coe_nonempty.mp ⟨x,PlaqueSystem.Reachable.refl L.plaques x⟩)
      Compacts.isClopen_singleton_bot.isOpen.isClosed_compl) hK
  exact hh

lemma leafLimits_saturated {K : Compacts X.Carrier} (hK : K∈L.leafLimits e hRC hdim)
    {z : X.Carrier} {U : Set (S.FirstModel z)} {V : Set (S.SecondModel z)}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hV : IsOpen V)
    (hT : U ×ˢ V⊆(L.chart z).chart.target)
    {a₀ a₁ : S.FirstModel z} {b : S.SecondModel z}
    (ha₀ : a₀∈U) (ha₁ : a₁∈U) (hb : b∈V)
    (hx : (L.chart z).chart.symm (a₀,b)∈(K : Set X.Carrier)) :
    (L.chart z).chart.symm (a₁,b)∈(K : Set X.Carrier) := by
  let P := (L.chart z).chart
  let W := P.source ∩ P ⁻¹' (U ×ˢ V)
  let f : X.Carrier → X.Carrier := fun y => P.symm (a₁,(P y).2)
  have hW : IsOpen W := P.continuousOn.isOpen_inter_preimage P.open_source (hU.prod hV)
  have hf : ContinuousOn f W := by
    intro y hy
    apply ContinuousAt.continuousWithinAt
    exact ContinuousAt.comp (f := fun y => (a₁,(P y).2)) (g := P.symm)
      (P.symm.continuousAt (hT ⟨ha₁,hy.2.2⟩))
      (continuousAt_const.prodMk (P.continuousAt hy.1).snd)
  have hInv : ∀y∈(K : Set X.Carrier),y∈W → f y∈(K : Set X.Carrier) := by
    apply (closure_minimal (t := {K : Compacts X.Carrier |
      ∀y∈(K : Set X.Carrier),y∈W → f y∈(K : Set X.Carrier)}) ?_
      (CompactSetLimits.isClosed_local_invariance hW hf)) hK
    rintro _ ⟨x,rfl⟩ y hy hyW
    apply L.plaques.leaf_saturated hy
    have hh := L.plaques.related_in_rectangle (i := z) hUc hT hyW.2.1 ha₁ hyW.2.2
    change L.plaques.Related (P.symm (P y)) (f y) at hh
    rwa [P.left_inv hyW.1] at hh
  have ht₀ := hT (show (a₀,b)∈U ×ˢ V from ⟨ha₀,hb⟩)
  have hh := hInv (P.symm (a₀,b)) hx ⟨P.map_target ht₀,by
    change P (P.symm (a₀,b))∈U ×ˢ V
    rw [P.right_inv ht₀]
    exact ⟨ha₀,hb⟩⟩
  simpa only [f,P.right_inv ht₀] using hh

end SplitTangent.LeafJetAtlas

end

end OAI
