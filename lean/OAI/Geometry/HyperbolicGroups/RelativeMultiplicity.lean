import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkMultiplicity
import OAI.Geometry.HyperbolicGroups.RelativeRawPosition
import OAI.Geometry.HyperbolicGroups.RelativeFanCapacity
import OAI.Geometry.HyperbolicGroups.RelativeInstanceAt

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

abbrev RawPositionSide (p : RawPosition n w d) := {x : P.Dart // select (P.faceClass x) = true ∧
  isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) = true ∧ stepPosition n w d ell hell word c hc f (P.index x) = some p}
noncomputable instance (p : RawPosition n w d) : Fintype (RawPositionSide n w d ell hell word c hc f P select p) :=
  Fintype.ofFinite _

abbrev KindFace (k : WalkKind n w d) := {F : P.Face // select F = true ∧ P.faceKind F = .inl k}
noncomputable instance (k : WalkKind n w d) : Fintype (KindFace n w d ell hell word c hc f P select k) :=
  Fintype.ofFinite _

/-- Top loose fields and every decoration field occur at most once in each
selected source face of that occurrence. -/
lemma raw_multiplicity_le_faces (hs : P.Simple) (hb : P.NoBigon)
    (hm : P.FrozenMapped (frozen n w d ell hell word c hc f)) (p : RawPosition n w d) :
    Fintype.card (RawPositionSide n w d ell hell word c hc f P select p) ≤
      Fintype.card (KindFace n w d ell hell word c hc f P select (walkKind n w d (rawRepresentative n w d p))) := by
  let g : RawPositionSide n w d ell hell word c hc f P select p →
      KindFace n w d ell hell word c hc f P select (walkKind n w d (rawRepresentative n w d p)) := fun x =>
    ⟨P.faceClass x.val,x.property.1,by
      obtain ⟨s,hi,hp⟩ := stepPosition_some n w d ell hell word c hc f P x.property.2.2
      change (target n w d ell hell word c hc f).kind (P.index x.val) = _
      rw [hi]
      change Sum.inl (walkKind n w d s) = _
      rw [ConeSkeleton.raw_kind n w d s,hp]⟩
  apply Fintype.card_le_of_injective g
  intro x y h
  apply Subtype.ext
  exact raw_position_once_per_face n w d ell hell word c hc f P hs hb hm
    (P.faceClass_eq.mp (congrArg Subtype.val h)) x.property.2.1 y.property.2.1
    x.property.2.2 y.property.2.2

lemma raw_fan_index {x : P.Dart} {g : FanTriangle n w}
    (hr : isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) = true)
    (hp : stepPosition n w d ell hell word c hc f (P.index x) = some (.inr (.inl g))) :
    ∃ o, P.index x = .inl (.inr ⟨.inl g,o,(1 : Fin 3)⟩) := by
  obtain ⟨s,he,hp⟩ := stepPosition_some n w d ell hell word c hc f P hp
  rw [he] at hr
  cases s with
  | inl s => cases hp
  | inr s =>
    rcases s with ⟨k,o,i⟩
    rcases k with h | (q | q)
    · have hg : h = g := Sum.inl.inj (Sum.inr.inj hp)
      have hi := fan_letter_index n w d h o i hr
      subst h; subst i
      exact ⟨o,he⟩
    · cases hp
    · cases hp

lemma raw_fan_previous (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    {x : P.Dart} {g : FanTriangle n w} {o : Bool}
    (hx : P.index x = .inl (.inr ⟨.inl g,o,(1 : Fin 3)⟩)) :
    P.index (P.pairing.face⁻¹ x) = .inl (frozenCorner n w d g o) := by
  rw [P.frozen_previous_index (frozen n w d ell hell word c hc f) hm (by rw [hx]; rfl),hx]
  cases o <;> rfl

lemma raw_fan_previous_start (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (g : FanTriangle n w) (x : RawPositionSide n w d ell hell word c hc f P select (.inr (.inl g))) :
    start n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.face⁻¹ x.val))) = .inr g.1 := by
  obtain ⟨o,ho⟩ := raw_fan_index n w d ell hell word c hc f P x.property.2.1 x.property.2.2
  rw [raw_fan_previous n w d ell hell word c hc f P hm ho,frozenCorner_start]

/-- A fan field's selected copies inject into the ACTUAL represented apex
instances, not into an assumed nominal collection of links. -/
lemma raw_fan_multiplicity_le (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (g : FanTriangle n w) :
    Fintype.card (RawPositionSide n w d ell hell word c hc f P select (.inr (.inl g))) ≤
      Fintype.card (ApexInstance n w d ell hell word c hc f P select g.1) := by
  let j : RawPositionSide n w d ell hell word c hc f P select (.inr (.inl g)) →
      ApexInstance n w d ell hell word c hc f P select g.1 := fun x =>
    apexInstanceAt n w d ell hell word c hc f P select g.1 (P.pairing.face⁻¹ x.val)
      (by rw [P.faceClass_previous]; exact x.property.1)
      (raw_fan_previous_start n w d ell hell word c hc f P select hm g x)
  apply Fintype.card_le_of_injective j
  intro x y h
  obtain ⟨o,ho⟩ := raw_fan_index n w d ell hell word c hc f P x.property.2.1 x.property.2.2
  obtain ⟨p,hp⟩ := raw_fan_index n w d ell hell word c hc f P y.property.2.1 y.property.2.2
  have hv : P.vertexClass (P.pairing.face⁻¹ x.val) = P.vertexClass (P.pairing.face⁻¹ y.val) :=
    congrArg Subtype.val h
  have hh := fan_field_once n w d ell hell word c hc f P hm hred hrad
    (raw_fan_previous n w d ell hell word c hc f P hm ho) (raw_fan_previous n w d ell hell word c hc f P hm hp)
    (P.vertexClass_eq.mp hv)
  exact Subtype.ext ((P.pairing.face⁻¹).injective hh)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
