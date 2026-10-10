import Mathlib
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.CompactLeafQuotient
import OAI.Geometry.SplitTangent.GlobalTopologicalProduct
import OAI.Geometry.SplitTangent.LeafProducts
import OAI.Geometry.SplitTangent.HolomorphicLeafBasic
import OAI.Geometry.SplitTangent.RationalVariation

namespace OAI

/-! Integrability Reduction. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent
namespace LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (M : LeafJetAtlas S.swap) (e : ProjectiveEmbedding X)
  (hRC : RationallyConnected e) (hdim : 0<X.dim)

lemma leafPair_injective_of_compatible_projective_product
    (hproduct : HasCompatibleProjectiveProduct X S) :
    Function.Injective (L.leafPair M e hRC hdim) := by
  obtain ⟨Y,Z,_,_,f,halign⟩ := hproduct
  let I := (ModelWithCorners Y).prod (ModelWithCorners Z)
  let p : X.Carrier → Y.Carrier := Prod.fst ∘ f
  let q : X.Carrier → Z.Carrier := Prod.snd ∘ f
  have hp : ContMDiff (ModelWithCorners X) (ModelWithCorners Y) ω p :=
    contMDiff_fst.comp f.contMDiff
  have hq : ContMDiff (ModelWithCorners X) (ModelWithCorners Z) ω q :=
    contMDiff_snd.comp f.contMDiff
  have hp0 : ∀x v,v∈S.swap.first x →
      mfderiv (ModelWithCorners X) (ModelWithCorners Y) p x v=0 := by
    intro x v hv
    rw [S.swap_first] at hv
    have hm := Submodule.mem_map_of_mem (f :=
      (mfderiv (ModelWithCorners X) I f x).toLinearMap) hv
    rw [(halign x).2] at hm
    change (mfderiv (ModelWithCorners X) I f x v).1=0 at hm
    change mfderiv (ModelWithCorners X) (ModelWithCorners Y) (Prod.fst ∘ f) x v=0
    rw [mfderiv_comp x mdifferentiableAt_fst
      ((f.contMDiff x).mdifferentiableAt (by simp)),mfderiv_fst]
    exact hm
  have hq0 : ∀x v,v∈S.first x →
      mfderiv (ModelWithCorners X) (ModelWithCorners Z) q x v=0 := by
    intro x v hv
    have hm := Submodule.mem_map_of_mem (f :=
      (mfderiv (ModelWithCorners X) I f x).toLinearMap) hv
    rw [(halign x).1] at hm
    change (mfderiv (ModelWithCorners X) I f x v).2=0 at hm
    change mfderiv (ModelWithCorners X) (ModelWithCorners Z) (Prod.snd ∘ f) x v=0
    rw [mfderiv_comp x mdifferentiableAt_snd
      ((f.contMDiff x).mdifferentiableAt (by simp)),mfderiv_snd]
    exact hm
  intro x y hxy
  have hL := (L.leafQuotient_eq_iff e hRC hdim x y).mp (congrArg Prod.fst hxy)
  have hM := (M.leafQuotient_eq_iff e hRC hdim x y).mp (congrArg Prod.snd hxy)
  apply f.injective
  exact Prod.ext (M.holomorphic_map_eq_on_leaf hp hp0 hM)
    (L.holomorphic_map_eq_on_leaf hq hq0 hL)

 

theorem compatible_projective_product_iff_leafPair_injective :
    HasCompatibleProjectiveProduct X S ↔ Function.Injective (L.leafPair M e hRC hdim) :=
  ⟨L.leafPair_injective_of_compatible_projective_product M e hRC hdim,
    L.compatible_projective_product_of_leafPair_injective M e hRC hdim⟩

lemma leafPair_injective_iff_single_intersection :
    Function.Injective (L.leafPair M e hRC hdim) ↔
      ∀x y,y∈L.leaf x → y∈M.leaf x → y=x := by
  constructor
  · intro h x y hL hM
    apply h
    exact Prod.ext ((L.leafQuotient_eq_iff e hRC hdim x y).mpr hL).symm
      ((M.leafQuotient_eq_iff e hRC hdim x y).mpr hM).symm
  · intro h x y hxy
    exact (h x y ((L.leafQuotient_eq_iff e hRC hdim x y).mp (congrArg Prod.fst hxy))
      ((M.leafQuotient_eq_iff e hRC hdim x y).mp (congrArg Prod.snd hxy))).symm

end LeafJetAtlas

 

def LeafPairOneSheetedStatement : Prop :=
  ∀ (X : ComplexManifold.{u}) [ConnectedSpace X.Carrier] [CompactSpace X.Carrier],
    ∀ (hd : 2≤X.dim), ∀(e : ProjectiveEmbedding X) (hRC : RationallyConnected e)
      (S : TangentSplitting X) (L : LeafJetAtlas S) (M : LeafJetAtlas S.swap),
      Function.Injective (L.leafPair M e hRC (by omega))

 

theorem main_iff_leafPair_oneSheeted : MainStatement.{u} ↔ LeafPairOneSheetedStatement.{u} := by
  constructor
  · intro h X hc hk hd e hRC S L M
    let := hc
    let := hk
    exact L.leafPair_injective_of_compatible_projective_product M e hRC (by omega)
      (h X hc hk hd e hRC S).2.2
  · intro h X hc hk hd e hRC S
    let := hc
    let := hk
    obtain ⟨h₁,h₂⟩ := S.integrable_of_rationallyConnected e hRC hd
    let L := S.leafJetAtlas h₁ h₂
    let M := S.swap.leafJetAtlas (by simpa only [S.swap_first] using h₂)
      (by simpa only [S.swap_second] using h₁)
    exact ⟨h₁,h₂,L.compatible_projective_product_of_leafPair_injective M e hRC
      (by omega) (@h X hc hk hd e hRC S L M)⟩

end SplitTangent

end

end OAI
