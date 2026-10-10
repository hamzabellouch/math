import Mathlib
import OAI.Geometry.HyperbolicGroups.FragmentSlots
import OAI.Geometry.HyperbolicGroups.RelativeFanLink

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

abbrev SelectedTopFace := {F : P.Face // select F = true ∧ ∃ a : Top n w, P.faceKind F = .inl (.inl a)}
noncomputable instance : Fintype (SelectedTopFace n w d ell hell word c hc f P select) := Fintype.ofFinite _

def faceOccurrence (F : SelectedTopFace n w d ell hell word c hc f P select) : Top n w := F.property.2.choose
lemma faceOccurrence_kind (F : SelectedTopFace n w d ell hell word c hc f P select) :
    P.faceKind F.val = .inl (.inl (faceOccurrence n w d ell hell word c hc f P select F)) := F.property.2.choose_spec

def topSlot (F : SelectedTopFace n w d ell hell word c hc f P select) (i : Fin 7) :
    Σ b : Fan n w, SelectedTop n w d ell hell word c hc f P select b :=
  ⟨slot n w (faceOccurrence n w d ell hell word c hc f P select F) i,
    F.val,F.property.1,faceOccurrence n w d ell hell word c hc f P select F,
    faceOccurrence_kind n w d ell hell word c hc f P select F,i,rfl⟩

lemma topSlot_injective : Function.Injective
    (fun p : SelectedTopFace n w d ell hell word c hc f P select × Fin 7 => topSlot n w d ell hell word c hc f P select p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z : Σ b : Fan n w, SelectedTop n w d ell hell word c hc f P select b => z.2.val) h
  · exact congrArg (fun z : Σ b : Fan n w, SelectedTop n w d ell hell word c hc f P select b => z.1.val.1) h

lemma topSlot_surjective : Function.Surjective
    (fun p : SelectedTopFace n w d ell hell word c hc f P select × Fin 7 => topSlot n w d ell hell word c hc f P select p.1 p.2) := by
  rintro ⟨b,F⟩
  obtain ⟨a,ha,i,hi⟩ := F.property.2
  let H : SelectedTopFace n w d ell hell word c hc f P select := ⟨F.val,F.property.1,a,ha⟩
  have hocc : faceOccurrence n w d ell hell word c hc f P select H = a :=
    Sum.inl.inj (Sum.inl.inj ((faceOccurrence_kind n w d ell hell word c hc f P select H).symm.trans ha))
  have hslot : slot n w (faceOccurrence n w d ell hell word c hc f P select H) i = b := by rw [hocc,hi]
  refine ⟨(H,i),?_⟩
  apply Sigma.ext hslot
  apply (Subtype.heq_iff_coe_eq (fun z => by change (select z = true ∧ ∃ a, P.faceKind z = .inl (.inl a) ∧ ∃ j, slot n w a j = slot n w (faceOccurrence n w d ell hell word c hc f P select H) i) ↔ _; rw [hslot])).mpr
  rfl

/-- Each selected top polygon contributes all seven indexed fan slots,
including the fan slots its simple boundary omits. -/
theorem fragment_slots_eq :
    (∑ b : Fan n w, Fintype.card (SelectedTop n w d ell hell word c hc f P select b)) =
      7 * Fintype.card (SelectedTopFace n w d ell hell word c hc f P select) := by
  rw [← Fintype.card_sigma]
  have h := Fintype.card_congr (Equiv.ofBijective _
    ⟨topSlot_injective n w d ell hell word c hc f P select,topSlot_surjective n w d ell hell word c hc f P select⟩)
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using h.symm

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
