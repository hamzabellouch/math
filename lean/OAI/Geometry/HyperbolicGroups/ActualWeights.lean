import Mathlib
import OAI.Geometry.HyperbolicGroups.RestrictOccurrence
import OAI.Geometry.HyperbolicGroups.ActualPosition
import OAI.Geometry.HyperbolicGroups.WalkMultiplicity
import OAI.Geometry.HyperbolicGroups.IndexedFanCounts
import OAI.Geometry.HyperbolicGroups.ConeApexProducer

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
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma top_count_le_slot (a : Top n w) (i : Fin 7) :
    Fintype.card (KindFace n w d c hc f P select (.inl a)) ≤
      (indexedFanData n w d c hc f P select (slot n w a i) hs hm hred hrad).weight := by
  by_cases he : Nonempty (KindFace n w d c hc f P select (.inl a))
  · let F := Classical.choice he
    let ao : SelectedOccurrence n w d c hc f P select := ⟨a,F.val,F.property⟩
    let b := slot n w a i
    let D := indexedFanData n w d c hc f P select b hs hm hred hrad
    let g : KindFace n w d c hc f P select (.inl a) →
        {H : SelectedTop n w d c hc f P select b // D.occurrence H = ao} := fun H =>
      ⟨⟨H.val,H.property.1,a,H.property.2,i,rfl⟩,by
        apply Subtype.ext
        exact Sum.inl.inj ((selectedOccurrence_kind n w d c hc f P select b _).symm.trans H.property.2)⟩
    have hcount : Fintype.card (KindFace n w d c hc f P select (.inl a)) ≤ D.multiplicity ao := by
      apply Fintype.card_le_of_injective g
      intro H K h
      exact Subtype.ext (congrArg (fun z => z.val.val) h)
    exact hcount.trans ((Finset.le_sup (f := D.multiplicity) (Finset.mem_univ ao)).trans (le_max_right _ _))
  · have hi : IsEmpty (KindFace n w d c hc f P select (.inl a)) := not_nonempty_iff.mp he
    have hzero : Fintype.card (KindFace n w d c hc f P select (.inl a)) = 0 := Fintype.card_eq_zero_iff.mpr hi
    rw [hzero]
    exact Nat.zero_le _

lemma indexed_weight_congr {b b' : Fan n w} (h : b = b') :
    (indexedFanData n w d c hc f P select b hs hm hred hrad).weight =
    (indexedFanData n w d c hc f P select b' hs hm hred hrad).weight := by
  cases h
  rfl

/-- Weights are the literal selected-face multiplicities and maximum of actual
apex count / same-top slot multiplicity. No contact capacity is a field. -/
def actualWeights : (occurrenceShape n w).Weights (v := Fintype.card (Six n d)) where
  top := fun a => Fintype.card (KindFace n w d c hc f P select (.inl ((enumTop n w).symm a)))
  fan := fun b => (indexedFanData n w d c hc f P select ((enumFan n w).symm b) hs hm hred hrad).weight
  square := fun q => Fintype.card (KindFace n w d c hc f P select (.inr (.inr (.inl ((enumSquare n w).symm q)))))
  six := fun q => Fintype.card (KindFace n w d c hc f P select (.inr (.inr (.inr ((enumSix n d).symm q)))))
  slot := by
    intro a i
    change _ ≤ (indexedFanData n w d c hc f P select
      ((enumFan n w).symm ((enumFan n w) (slot n w ((enumTop n w).symm a) i))) hs hm hred hrad).weight
    rw [indexed_weight_congr n w d c hc f P select hs hm hred hrad ((enumFan n w).symm_apply_apply _)]
    exact top_count_le_slot n w d c hc f P select hs hm hred hrad _ i

lemma actual_position_capacity (hb : P.NoBigon) (p : RawPosition n w d) :
    Fintype.card (RawPositionSide n w d c hc f P select p) ≤
      (actualWeights n w d c hc f P select hs hm hred hrad).position (rawToPosition n w d p) := by
  rcases p with a | (g | (⟨q,i⟩ | ⟨q,i⟩))
  · have hh := raw_multiplicity_le_faces n w d c hc f P select hs hb hm (.inl a)
    simp only [← Nat.card_eq_fintype_card] at hh
    simpa only [actualWeights,Occurrences.Shape.Weights.position,rawToPosition,Equiv.symm_apply_apply,
      rawRepresentative,walkKind,FanLink.IndexedFanData.weight, ← Nat.card_eq_fintype_card] using hh
  · have hh := raw_fan_multiplicity_le n w d c hc f P select hm hred hrad g
    change _ ≤ (indexedFanData n w d c hc f P select
      ((enumFan n w).symm ((enumFan n w) g.1)) hs hm hred hrad).weight
    rw [indexed_weight_congr n w d c hc f P select hs hm hred hrad ((enumFan n w).symm_apply_apply _)]
    exact hh.trans (le_max_left _ _)
  · have hh := raw_multiplicity_le_faces n w d c hc f P select hs hb hm (.inr (.inr (.inl (q,i))))
    simp only [← Nat.card_eq_fintype_card] at hh
    simpa only [actualWeights,Occurrences.Shape.Weights.position,rawToPosition,Equiv.symm_apply_apply,
      rawRepresentative,walkKind,FanLink.IndexedFanData.weight, ← Nat.card_eq_fintype_card] using hh
  · have hh := raw_multiplicity_le_faces n w d c hc f P select hs hb hm (.inr (.inr (.inr (q,i))))
    simp only [← Nat.card_eq_fintype_card] at hh
    simpa only [actualWeights,Occurrences.Shape.Weights.position,rawToPosition,Equiv.symm_apply_apply,
      rawRepresentative,walkKind,FanLink.IndexedFanData.weight, ← Nat.card_eq_fintype_card] using hh

end HyperbolicObstruction.ConeSkeleton
end

end OAI
