import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkInstanceAt
import OAI.Geometry.HyperbolicGroups.ConeApexProducer
import OAI.Geometry.HyperbolicGroups.WalkTopTurns
import OAI.Geometry.HyperbolicGroups.IndexedFanCards

namespace OAI

section
section


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
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)


variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev AllTurnIndex := Σ b : Fan n w,
  (indexedFanData n w d c hc f P select b hs hm hred hrad).TurnIndex

def allTurnDart (p : AllTurnIndex n w d c hc f P select hs hm hred hrad) :
    TopTurnDart n w d c hc f P select := by
  refine ⟨p.2.val.2.val,?_,instance_apex n w d c hc f P select p.1 p.2.val.1 p.2.val.2,?_⟩
  · by_contra hh
    have he := (mark_absent n w d c hc f P select p.1 p.2.val.1 p.2.val.2).mpr hh
    obtain ⟨F,hF⟩ := p.2.property
    change fragmentMark n w d c hc f P select p.1 p.2.val.1 p.2.val.2 = .top F at hF
    rw [he] at hF
    cases hF
  · obtain ⟨F,hF⟩ := p.2.property
    obtain ⟨e,he⟩ := mark_top_index n w d c hc f P select p.1 p.2.val.1 p.2.val.2 F hF
    rw [he]; rfl

lemma allTurnDart_surjective : Function.Surjective
    (allTurnDart n w d c hc f P select hs hm hred hrad) := by
  intro x
  obtain ⟨b,hb⟩ : ∃ b, start n w (walkLabel n w d (P.index x.val)) = .inr b := by
    cases he : start n w (walkLabel n w d (P.index x.val)) with
    | inl a => have hh := x.property.2.1; rw [he] at hh; cases hh
    | inr b => exact ⟨b,rfl⟩
  let z := apexInstanceAt n w d c hc f P select b x.val x.property.1 hb
  let y : P.Link z.val := ⟨x.val,rfl⟩
  have ht : ∃ a e, P.index x.val = .inl (a,e) := by
    cases he : P.index x.val with
    | inl s => exact ⟨s.1,s.2,rfl⟩
    | inr s => have hh := x.property.2.2; rw [he] at hh; cases hh
  have hmark : ∃ F, fragmentMark n w d c hc f P select b z y = .top F := by
    unfold fragmentMark
    exact ⟨_,by rw [dite_eq_left x.property.1,dite_eq_left ht]⟩
  exact ⟨⟨b,⟨⟨z,y⟩,hmark⟩⟩,Subtype.ext rfl⟩

lemma allTurnIndex_card :
    Fintype.card (AllTurnIndex n w d c hc f P select hs hm hred hrad) =
      ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).turns := by
  rw [← Nat.card_eq_fintype_card]
  exact FanLink.IndexedFanData.family_natTurnIndex_card
    (fun b => indexedFanData n w d c hc f P select b hs hm hred hrad)

/-- All selected top apex darts are really fan turns. Together with the
actual macro cycle bound this supplies the source `sum d_z >= 3T`. -/
theorem actual_turns_ge (hb : P.NoBigon) :
    3 * Fintype.card (SelectedTopFace n w d c hc f P select) ≤
      ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).turns := by
  have h1 := selected_top_turns_ge n w d c hc f P select hs hb
  have h2 := Fintype.card_le_of_surjective _
    (allTurnDart_surjective n w d c hc f P select hs hm hred hrad)
  exact h1.trans (h2.trans_eq (allTurnIndex_card n w d c hc f P select hs hm hred hrad))

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
