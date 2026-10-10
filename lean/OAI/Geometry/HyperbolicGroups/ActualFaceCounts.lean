import Mathlib
import OAI.Geometry.HyperbolicGroups.ActualWeights
import OAI.Geometry.HyperbolicGroups.FragmentSlots
import OAI.Geometry.HyperbolicGroups.WalkTriangleTransport

namespace OAI

noncomputable section

open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)

lemma count_faces_in {K : Type*} [Fintype K] (g : K → WalkKind n w d) (hg : Function.Injective g) :
    (∑ k, Fintype.card (KindFace n w d c hc f P select (g k))) =
      Fintype.card {F : P.Face // select F = true ∧ ∃ k, P.faceKind F = g k} := by
  rw [← Fintype.card_sigma]
  let v : (Σ k, KindFace n w d c hc f P select (g k)) →
      {F : P.Face // select F = true ∧ ∃ k, P.faceKind F = g k} :=
    fun p => ⟨p.2.val,p.2.property.1,p.1,p.2.property.2⟩
  apply Fintype.card_congr (Equiv.ofBijective v ?_)
  constructor
  · rintro ⟨k,F⟩ ⟨l,G⟩ h
    have hFG : F.val = G.val := congrArg Subtype.val h
    have hkl : k = l := hg (F.property.2.symm.trans ((congrArg P.faceKind hFG).trans G.property.2))
    subst l
    have hh : F = G := Subtype.ext hFG
    subst G
    rfl
  · rintro ⟨F,hF,k,hk⟩
    exact ⟨⟨k,F,hF,hk⟩,rfl⟩

abbrev SelectedFace := {F : P.Face // select F = true}
noncomputable instance : Fintype (SelectedFace n w d c hc f P select) := Fintype.ofFinite _

def actualTopCount : ℕ := Fintype.card (SelectedTopFace n w d c hc f P select)
def actualTriangleCount : ℕ := Fintype.card (SelectedTriangleFace n w d c hc f P select)
def actualSquareCount : ℕ := ∑ q : Square n w, Fintype.card (KindFace n w d c hc f P select (.inr (.inr (.inl q))))
def actualSixCount : ℕ := ∑ q : Six n d, Fintype.card (KindFace n w d c hc f P select (.inr (.inr (.inr q))))
def actualArea : ℕ := Fintype.card (SelectedFace n w d c hc f P select)

lemma sum_top_count : (∑ a : Top n w, Fintype.card (KindFace n w d c hc f P select (.inl a))) =
    actualTopCount n w d c hc f P select := by
  simpa only [actualTopCount,← Nat.card_eq_fintype_card] using
    count_faces_in n w d c hc f P select Sum.inl Sum.inl_injective
lemma sum_triangle_count : (∑ g : FanTriangle n w, Fintype.card (KindFace n w d c hc f P select (.inr (.inl g)))) =
    actualTriangleCount n w d c hc f P select := by
  simpa only [actualTriangleCount,Function.comp_apply,← Nat.card_eq_fintype_card] using
    count_faces_in n w d c hc f P select (Sum.inr ∘ Sum.inl) (Sum.inr_injective.comp Sum.inl_injective)

lemma actual_area_eq : actualArea n w d c hc f P select = actualTopCount n w d c hc f P select +
    actualTriangleCount n w d c hc f P select + actualSquareCount n w d c hc f P select +
    actualSixCount n w d c hc f P select := by
  have hh := count_faces_in n w d c hc f P select id Function.injective_id
  have he : Fintype.card {F : P.Face // select F = true ∧ ∃ k, P.faceKind F = id k} =
      actualArea n w d c hc f P select := by
    apply Fintype.card_congr
    exact { toFun := fun F => ⟨F.val,F.property.1⟩
            invFun := fun F => ⟨F.val,F.property,P.faceKind F.val,rfl⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  rw [he] at hh
  simp only [id_eq,Fintype.sum_sum_type] at hh
  rw [sum_top_count n w d c hc f P select,sum_triangle_count n w d c hc f P select] at hh
  unfold actualSquareCount actualSixCount
  omega

variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_weights_top : (∑ a, (actualWeights n w d c hc f P select hs hm hred hrad).top a) =
    actualTopCount n w d c hc f P select := by
  change (∑ a, Fintype.card (KindFace n w d c hc f P select (.inl ((enumTop n w).symm a)))) = _
  exact (Equiv.sum_comp (enumTop n w).symm (fun a => Fintype.card (KindFace n w d c hc f P select (.inl a)))).trans
    (sum_top_count n w d c hc f P select)
lemma actual_weights_square : (∑ q, (actualWeights n w d c hc f P select hs hm hred hrad).square q) =
    actualSquareCount n w d c hc f P select := by
  exact Equiv.sum_comp (enumSquare n w).symm (fun q => Fintype.card (KindFace n w d c hc f P select (.inr (.inr (.inl q)))))
lemma actual_weights_six : (∑ q, (actualWeights n w d c hc f P select hs hm hred hrad).six q) =
    actualSixCount n w d c hc f P select := by
  exact Equiv.sum_comp (enumSix n d).symm (fun q => Fintype.card (KindFace n w d c hc f P select (.inr (.inr (.inr q)))))
lemma actual_weights_fan : (∑ b, (actualWeights n w d c hc f P select hs hm hred hrad).fan b) =
    ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).weight := by
  exact Equiv.sum_comp (enumFan n w).symm (fun b => (indexedFanData n w d c hc f P select b hs hm hred hrad).weight)

end HyperbolicObstruction.ConeSkeleton
end

end OAI
