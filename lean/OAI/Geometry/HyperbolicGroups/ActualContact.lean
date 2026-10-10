import Mathlib
import OAI.Geometry.HyperbolicGroups.ActualWeights
import OAI.Geometry.HyperbolicGroups.ActualLabel
import OAI.Geometry.HyperbolicGroups.ContactCapacity
import OAI.Geometry.HyperbolicGroups.LocalWeightedRank

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

def selectedDart (x : P.Dart) : Prop := select (P.faceClass x) = true
def rawDart (x : P.Dart) : Prop := isLetter n w (walkLabel n w d (P.index x)) = true
lemma rawDart_pair (x : P.Dart) : rawDart n w d c hc f P (P.pairing.edge x) ↔ rawDart n w d c hc f P x := by
  unfold rawDart
  have h : walkLabel n w d (P.index (P.pairing.edge x)) = rev n w (walkLabel n w d (P.index x)) := P.paired x
  rw [h]
  rfl

abbrev ActualContact := P.pairing.Contact (selectedDart n w d c hc f P select) (rawDart n w d c hc f P)
abbrev ActualRawSide := PictureMap.SelectedSide (selectedDart n w d c hc f P select) (rawDart n w d c hc f P)
abbrev ActualRawBoundary := P.pairing.BoundarySide (selectedDart n w d c hc f P select) (rawDart n w d c hc f P)
def contactLeft (e : ActualContact n w d c hc f P select) := rawToPosition n w d (rawPosition n w d (P.index e.val))
def contactRight (e : ActualContact n w d c hc f P select) := rawToPosition n w d (rawPosition n w d (P.index (P.pairing.edge e.val)))

lemma actual_contact_ne (hred : P.FullyReduced) (e : ActualContact n w d c hc f P select) :
    contactLeft n w d c hc f P select e ≠ contactRight n w d c hc f P select e := by
  intro h
  exact contact_different n w d c hc f P hred e.val e.property.1 ((rawToPosition_injective n w d) h)

lemma actual_contact_value (e : ActualContact n w d c hc f P select) :
    (occurrenceValues n w d (contactLeft n w d c hc f P select e)).1 =
      (occurrenceValues n w d (contactRight n w d c hc f P select e)).1 := by
  have hl := raw_label_value n w d (P.index e.val) e.property.1
  have hr := raw_label_value n w d (P.index (P.pairing.edge e.val))
    ((rawDart_pair n w d c hc f P e.val).mpr e.property.1)
  have he := congrArg Prod.fst (P.paired e.val)
  have hh : Sum.inl ((occurrenceValues n w d (contactRight n w d c hc f P select e)).1) =
      (Sum.inl ((occurrenceValues n w d (contactLeft n w d c hc f P select e)).1) : ConeSkeleton.Edge n w) := by
    exact hr.symm.trans (he.trans hl)
  exact (Sum.inl.inj hh).symm

variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_contact_capacity (hb : P.NoBigon) (p : (occurrenceShape n w).Pos (Fintype.card (Six n d))) :
    (Finset.univ.filter (fun e : ActualContact n w d c hc f P select =>
      contactLeft n w d c hc f P select e = p ∨ contactRight n w d c hc f P select e = p)).card ≤
      (actualWeights n w d c hc f P select hs hm hred hrad).position p := by
  obtain ⟨r,rfl⟩ := rawToPosition_surjective n w d p
  have heq (e : ActualContact n w d c hc f P select) :
      (contactLeft n w d c hc f P select e = rawToPosition n w d r ∨
      contactRight n w d c hc f P select e = rawToPosition n w d r) ↔
      (rawPosition n w d (P.index e.val) = r ∨ rawPosition n w d (P.index (P.pairing.edge e.val)) = r) := by
    simp only [contactLeft,contactRight,(rawToPosition_injective n w d).eq_iff]
  simp_rw [heq]
  rw [← Fintype.card_subtype]
  have hh := P.pairing.contact_capacity (selectedDart n w d c hc f P select) (rawDart n w d c hc f P)
    (rawDart_pair n w d c hc f P) (fun x => rawPosition n w d (P.index x)) r
  have hcard : Fintype.card (PictureMap.PositionSide (selectedDart n w d c hc f P select)
      (rawDart n w d c hc f P) (fun x => rawPosition n w d (P.index x)) r) =
      Fintype.card (RawPositionSide n w d c hc f P select r) := by
    apply Fintype.card_congr
    exact { toFun := fun x => ⟨x.val.val,x.val.property.2,x.val.property.1,x.property⟩
            invFun := fun x => ⟨⟨x.val,x.property.2.1,x.property.1⟩,x.property.2.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  rw [hcard] at hh
  simpa only [← Nat.card_eq_fintype_card] using
    hh.trans (actual_position_capacity n w d c hc f P select hs hm hred hrad hb r)

/-- The contact-counting estimate for the literal normalized mixed picture.
Only the stochastic rank event and layer-size bounds remain here; no side
capacity, radial accounting, or label-incidence premise is assumed. -/
theorem actual_contact_bound {M : ℕ} {α β δ : ℝ}
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d)) (hb : P.NoBigon)
    (ht : ∀ j, Fintype.card ((actualWeights n w d c hc f P select hs hm hred hrad).TopAt j) ≤ M)
    (hf : ∀ j, Fintype.card ((actualWeights n w d c hc f P select hs hm hred hrad).FanAt j) ≤ M)
    (hq : ∀ j, Fintype.card ((actualWeights n w d c hc f P select hs hm hred hrad).SquareAt j) ≤ M)
    (hv : ∀ j, Fintype.card ((actualWeights n w d c hc f P select hs hm hred hrad).SixAt j) ≤ M) :
    let W := actualWeights n w d c hc f P select hs hm hred hrad
    (Fintype.card (ActualContact n w d c hc f P select) : ℝ) ≤
      ((3-β)-7*(2-α)) * (∑ a, (W.top a : ℝ)) + (2-α) * (∑ b, (W.fan b : ℝ)) +
      (2-δ) * (∑ q, (W.square q : ℝ)) + (3-δ) * (∑ q, (W.six q : ℝ)) := by
  let W := actualWeights n w d c hc f P select hs hm hred hrad
  let K := Finset.univ.sup W.top + Finset.univ.sup W.fan + Finset.univ.sup W.square + Finset.univ.sup W.six
  have htK (a) : W.top a ≤ K := by
    have h := Finset.le_sup (f := W.top) (Finset.mem_univ a)
    dsimp [K]; omega
  have hfK (b) : W.fan b ≤ K := by
    have h := Finset.le_sup (f := W.fan) (Finset.mem_univ b)
    dsimp [K]; omega
  have hqK (q) : W.square q ≤ K := by
    have h := Finset.le_sup (f := W.square) (Finset.mem_univ q)
    dsimp [K]; omega
  have hvK (q) : W.six q ≤ K := by
    have h := Finset.le_sup (f := W.six) (Finset.mem_univ q)
    dsimp [K]; omega
  exact W.contact_bound_local hgood ht hf hq hv (occurrenceValues n w d)
    (occurrence_row_injective n w d) (occurrence_present n w d) htK hfK hqK hvK
    (contactLeft n w d c hc f P select) (contactRight n w d c hc f P select)
    (actual_contact_ne n w d c hc f P select hred) (actual_contact_value n w d c hc f P select)
    (by
      intro p
      convert actual_contact_capacity n w d c hc f P select hs hm hred hrad hb p using 1
      exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _))

lemma actual_boundary_contacts_eq :
    Fintype.card (ActualRawBoundary n w d c hc f P select) +
      2 * Fintype.card (ActualContact n w d c hc f P select) =
    Fintype.card (ActualRawSide n w d c hc f P select) :=
  P.pairing.boundary_contacts_eq (selectedDart n w d c hc f P select) (rawDart n w d c hc f P)
    (rawDart_pair n w d c hc f P)

end HyperbolicObstruction.ConeSkeleton
end

end OAI
