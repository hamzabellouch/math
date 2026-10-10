import Mathlib
import OAI.Geometry.HyperbolicGroups.ActualContact
import OAI.Geometry.HyperbolicGroups.RelativeWeights

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

def selectedDart (x : P.Dart) : Prop := select (P.faceClass x) = true
def rawDart (x : P.Dart) : Prop := isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) = true
lemma rawDart_pair (x : P.Dart) : rawDart n w d ell hell word c hc f P (P.pairing.edge x) ↔ rawDart n w d ell hell word c hc f P x := by
  unfold rawDart
  have h : (target n w d ell hell word c hc f).label (P.index (P.pairing.edge x)) = rev n w ((target n w d ell hell word c hc f).label (P.index x)) := P.paired x
  rw [h]
  rfl

abbrev ActualContact := P.pairing.Contact (selectedDart n w d ell hell word c hc f P select) (rawDart n w d ell hell word c hc f P)
abbrev ActualRawSide := PictureMap.SelectedSide (selectedDart n w d ell hell word c hc f P select) (rawDart n w d ell hell word c hc f P)
abbrev ActualRawBoundary := P.pairing.BoundarySide (selectedDart n w d ell hell word c hc f P select) (rawDart n w d ell hell word c hc f P)

/-- Only genuine disk-interior cells belong to a fragment. -/
def InteriorSelection : Prop := ∀ F : P.Face, select F = true → ∃ k, P.faceKind F = .inl k

variable (hsel : InteriorSelection n w d ell hell word c hc f P select)

include hsel in
lemma selected_interior {x : P.Dart} (hx : selectedDart n w d ell hell word c hc f P select x) :
    ∃ s, P.index x = .inl s := by
  obtain ⟨k,hk⟩ := hsel (P.faceClass x) hx
  change (target n w d ell hell word c hc f).kind (P.index x) = .inl k at hk
  cases hi : P.index x with
  | inl s => exact ⟨s,rfl⟩
  | inr s => rw [hi] at hk; cases hk

def selectedStep (x : P.Dart) (hx : selectedDart n w d ell hell word c hc f P select x) :
    WalkStep n w d := (selected_interior n w d ell hell word c hc f P select hsel hx).choose
lemma selectedStep_index (x : P.Dart) (hx : selectedDart n w d ell hell word c hc f P select x) :
    P.index x = .inl (selectedStep n w d ell hell word c hc f P select hsel x hx) :=
  (selected_interior n w d ell hell word c hc f P select hsel hx).choose_spec

def selectedPosition (x : P.Dart) (hx : selectedDart n w d ell hell word c hc f P select x) :
    RawPosition n w d := rawPosition n w d (selectedStep n w d ell hell word c hc f P select hsel x hx)
lemma selectedPosition_eq (x : P.Dart) (hx : selectedDart n w d ell hell word c hc f P select x) :
    stepPosition n w d ell hell word c hc f (P.index x) =
      some (selectedPosition n w d ell hell word c hc f P select hsel x hx) := by
  rw [selectedStep_index n w d ell hell word c hc f P select hsel x hx]
  rfl

lemma selectedPosition_value (x : P.Dart) (hx : selectedDart n w d ell hell word c hc f P select x)
    (hr : rawDart n w d ell hell word c hc f P x) :
    ((target n w d ell hell word c hc f).label (P.index x)).1 =
      .inl ((occurrenceValues n w d (rawToPosition n w d
        (selectedPosition n w d ell hell word c hc f P select hsel x hx))).1) := by
  have hi := selectedStep_index n w d ell hell word c hc f P select hsel x hx
  change isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) = true at hr
  rw [hi] at hr ⊢
  exact raw_label_value n w d _ hr

def contactLeft (e : ActualContact n w d ell hell word c hc f P select) :=
  rawToPosition n w d (selectedPosition n w d ell hell word c hc f P select hsel e.val e.property.2.1)
def contactRight (e : ActualContact n w d ell hell word c hc f P select) :=
  rawToPosition n w d (selectedPosition n w d ell hell word c hc f P select hsel
    (P.pairing.edge e.val) e.property.2.2.1)

lemma actual_contact_ne (hred : P.FullyReduced) (e : ActualContact n w d ell hell word c hc f P select) :
    contactLeft n w d ell hell word c hc f P select hsel e ≠
      contactRight n w d ell hell word c hc f P select hsel e := by
  intro h
  have hp := (rawToPosition_injective n w d) h
  have hl := selectedPosition_eq n w d ell hell word c hc f P select hsel e.val e.property.2.1
  have hr := selectedPosition_eq n w d ell hell word c hc f P select hsel
    (P.pairing.edge e.val) e.property.2.2.1
  rw [← hp] at hr
  exact contact_position_different n w d ell hell word c hc f P hred e.property.1 hl hr

lemma actual_contact_value (e : ActualContact n w d ell hell word c hc f P select) :
    (occurrenceValues n w d (contactLeft n w d ell hell word c hc f P select hsel e)).1 =
      (occurrenceValues n w d (contactRight n w d ell hell word c hc f P select hsel e)).1 := by
  have hl := selectedPosition_value n w d ell hell word c hc f P select hsel
    e.val e.property.2.1 e.property.1
  have hr := selectedPosition_value n w d ell hell word c hc f P select hsel
    (P.pairing.edge e.val) e.property.2.2.1
    ((rawDart_pair n w d ell hell word c hc f P e.val).mpr e.property.1)
  have he := congrArg Prod.fst (P.paired e.val)
  exact (Sum.inl.inj (hr.symm.trans (he.trans hl))).symm

variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_contact_capacity (hb : P.NoBigon) (p : (occurrenceShape n w).Pos (Fintype.card (Six n d))) :
    (Finset.univ.filter (fun e : ActualContact n w d ell hell word c hc f P select =>
      contactLeft n w d ell hell word c hc f P select hsel e = p ∨
      contactRight n w d ell hell word c hc f P select hsel e = p)).card ≤
      (actualWeights n w d ell hell word c hc f P select hs hm hred hrad).position p := by
  obtain ⟨r,rfl⟩ := rawToPosition_surjective n w d p
  have heq (e : ActualContact n w d ell hell word c hc f P select) :
      (contactLeft n w d ell hell word c hc f P select hsel e = rawToPosition n w d r ∨
      contactRight n w d ell hell word c hc f P select hsel e = rawToPosition n w d r) ↔
      (stepPosition n w d ell hell word c hc f (P.index e.val) = some r ∨
      stepPosition n w d ell hell word c hc f (P.index (P.pairing.edge e.val)) = some r) := by
    rw [selectedPosition_eq n w d ell hell word c hc f P select hsel e.val e.property.2.1,
      selectedPosition_eq n w d ell hell word c hc f P select hsel (P.pairing.edge e.val) e.property.2.2.1]
    simp only [contactLeft,contactRight,(rawToPosition_injective n w d).eq_iff,Option.some.injEq]
  simp_rw [heq]
  rw [← Fintype.card_subtype]
  have hh := P.pairing.contact_capacity (selectedDart n w d ell hell word c hc f P select)
    (rawDart n w d ell hell word c hc f P) (rawDart_pair n w d ell hell word c hc f P)
    (fun x => stepPosition n w d ell hell word c hc f (P.index x)) (some r)
  have hcard : Fintype.card (PictureMap.PositionSide (selectedDart n w d ell hell word c hc f P select)
      (rawDart n w d ell hell word c hc f P)
      (fun x => stepPosition n w d ell hell word c hc f (P.index x)) (some r)) =
      Fintype.card (RawPositionSide n w d ell hell word c hc f P select r) := by
    apply Fintype.card_congr
    exact { toFun := fun x => ⟨x.val.val,x.val.property.2,x.val.property.1,x.property⟩
            invFun := fun x => ⟨⟨x.val,x.property.2.1,x.property.1⟩,x.property.2.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  simp only [← Nat.card_eq_fintype_card] at hcard hh
  rw [hcard] at hh
  have hp := actual_position_capacity n w d ell hell word c hc f P select hs hm hred hrad hb r
  simp only [← Nat.card_eq_fintype_card] at hp
  simpa only [← Nat.card_eq_fintype_card] using hh.trans hp

include hsel in
/-- The contact-counting estimate for the literal normalized mixed picture.
Only the stochastic rank event and layer-size bounds remain here; no side
capacity, radial accounting, or label-incidence premise is assumed. -/
theorem actual_contact_bound {M : ℕ} {α β δ : ℝ}
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d)) (hb : P.NoBigon)
    (ht : ∀ j, Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).TopAt j) ≤ M)
    (hf : ∀ j, Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).FanAt j) ≤ M)
    (hq : ∀ j, Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).SquareAt j) ≤ M)
    (hv : ∀ j, Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).SixAt j) ≤ M) :
    let W := actualWeights n w d ell hell word c hc f P select hs hm hred hrad
    (Fintype.card (ActualContact n w d ell hell word c hc f P select) : ℝ) ≤
      ((3-β)-7*(2-α)) * (∑ a, (W.top a : ℝ)) + (2-α) * (∑ b, (W.fan b : ℝ)) +
      (2-δ) * (∑ q, (W.square q : ℝ)) + (3-δ) * (∑ q, (W.six q : ℝ)) := by
  let W := actualWeights n w d ell hell word c hc f P select hs hm hred hrad
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
    (contactLeft n w d ell hell word c hc f P select hsel) (contactRight n w d ell hell word c hc f P select hsel)
    (actual_contact_ne n w d ell hell word c hc f P select hsel hred) (actual_contact_value n w d ell hell word c hc f P select hsel)
    (by
      intro p
      convert actual_contact_capacity n w d ell hell word c hc f P select hsel hs hm hred hrad hb p using 1
      exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _))

lemma actual_boundary_contacts_eq :
    Fintype.card (ActualRawBoundary n w d ell hell word c hc f P select) +
      2 * Fintype.card (ActualContact n w d ell hell word c hc f P select) =
    Fintype.card (ActualRawSide n w d ell hell word c hc f P select) :=
  P.pairing.boundary_contacts_eq (selectedDart n w d ell hell word c hc f P select) (rawDart n w d ell hell word c hc f P)
    (rawDart_pair n w d ell hell word c hc f P)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
