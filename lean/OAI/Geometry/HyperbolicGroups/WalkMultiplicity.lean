import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkFacePosition
import OAI.Geometry.HyperbolicGroups.WalkFanCapacity
import OAI.Geometry.HyperbolicGroups.WalkInstanceAt
import OAI.Geometry.HyperbolicGroups.FrozenPrevious

namespace OAI

section
section


noncomputable section
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

abbrev RawPositionSide (p : RawPosition n w d) := {x : P.Dart // select (P.faceClass x) = true ∧
  isLetter n w (walkLabel n w d (P.index x)) = true ∧ rawPosition n w d (P.index x) = p}
noncomputable instance (p : RawPosition n w d) : Fintype (RawPositionSide n w d c hc f P select p) :=
  Fintype.ofFinite _

abbrev KindFace (k : WalkKind n w d) := {F : P.Face // select F = true ∧ P.faceKind F = k}
noncomputable instance (k : WalkKind n w d) : Fintype (KindFace n w d c hc f P select k) :=
  Fintype.ofFinite _

lemma raw_kind (s : WalkStep n w d) : walkKind n w d s =
    walkKind n w d (rawRepresentative n w d (rawPosition n w d s)) := by
  rcases s with ⟨a,e⟩ | ⟨g,o,i⟩
  · rfl
  · rcases g with g | (q | q) <;> rfl

/-- Top loose fields and every decoration field occur at most once in each
selected source face of that occurrence. -/
lemma raw_multiplicity_le_faces (hs : P.Simple) (hb : P.NoBigon)
    (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f)) (p : RawPosition n w d) :
    Fintype.card (RawPositionSide n w d c hc f P select p) ≤
      Fintype.card (KindFace n w d c hc f P select (walkKind n w d (rawRepresentative n w d p))) := by
  let g : RawPositionSide n w d c hc f P select p →
      KindFace n w d c hc f P select (walkKind n w d (rawRepresentative n w d p)) := fun x =>
    ⟨P.faceClass x.val,x.property.1,by
      change walkKind n w d (P.index x.val) = _
      rw [raw_kind n w d (P.index x.val),x.property.2.2]⟩
  apply Fintype.card_le_of_injective g
  intro x y h
  apply Subtype.ext
  exact raw_position_once_per_face n w d c hc f P hs hb hm
    (P.faceClass_eq.mp (congrArg Subtype.val h)) x.property.2.1 y.property.2.1
    (x.property.2.2.trans y.property.2.2.symm)

lemma raw_fan_index {x : P.Dart} {g : FanTriangle n w}
    (hr : isLetter n w (walkLabel n w d (P.index x)) = true)
    (hp : rawPosition n w d (P.index x) = .inr (.inl g)) :
    ∃ o, P.index x = .inr ⟨.inl g,o,(1 : Fin 3)⟩ := by
  cases he : P.index x with
  | inl s => rw [he] at hp; cases hp
  | inr s =>
    rcases s with ⟨k,o,i⟩
    rcases k with h | (q | q)
    · rw [he] at hp hr
      have hg : h = g := Sum.inl.inj (Sum.inr.inj hp)
      have hi := fan_letter_index n w d h o i hr
      subst h; subst i
      exact ⟨o,rfl⟩
    · rw [he] at hp; cases hp
    · rw [he] at hp; cases hp

lemma raw_fan_previous (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    {x : P.Dart} {g : FanTriangle n w} {o : Bool}
    (hx : P.index x = .inr ⟨.inl g,o,(1 : Fin 3)⟩) :
    P.index (P.pairing.face⁻¹ x) = frozenCorner n w d g o := by
  rw [P.frozen_previous_index (walkFrozenTarget n w d c hc f) hm (by rw [hx]; rfl),hx]
  cases o <;> rfl

lemma raw_fan_previous_start (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (g : FanTriangle n w) (x : RawPositionSide n w d c hc f P select (.inr (.inl g))) :
    start n w (walkLabel n w d (P.index (P.pairing.face⁻¹ x.val))) = .inr g.1 := by
  obtain ⟨o,ho⟩ := raw_fan_index n w d c hc f P x.property.2.1 x.property.2.2
  rw [raw_fan_previous n w d c hc f P hm ho,frozenCorner_start]

/-- A fan field's selected copies inject into the ACTUAL represented apex
instances, not into an assumed nominal collection of links. -/
lemma raw_fan_multiplicity_le (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (g : FanTriangle n w) :
    Fintype.card (RawPositionSide n w d c hc f P select (.inr (.inl g))) ≤
      Fintype.card (ApexInstance n w d c hc f P select g.1) := by
  let j : RawPositionSide n w d c hc f P select (.inr (.inl g)) →
      ApexInstance n w d c hc f P select g.1 := fun x =>
    apexInstanceAt n w d c hc f P select g.1 (P.pairing.face⁻¹ x.val)
      (by rw [P.faceClass_previous]; exact x.property.1)
      (raw_fan_previous_start n w d c hc f P select hm g x)
  apply Fintype.card_le_of_injective j
  intro x y h
  obtain ⟨o,ho⟩ := raw_fan_index n w d c hc f P x.property.2.1 x.property.2.2
  obtain ⟨p,hp⟩ := raw_fan_index n w d c hc f P y.property.2.1 y.property.2.2
  have hv : P.vertexClass (P.pairing.face⁻¹ x.val) = P.vertexClass (P.pairing.face⁻¹ y.val) :=
    congrArg Subtype.val h
  have hh := fan_field_once n w d c hc f P hm hred hrad
    (raw_fan_previous n w d c hc f P hm ho) (raw_fan_previous n w d c hc f P hm hp)
    (P.vertexClass_eq.mp hv)
  exact Subtype.ext ((P.pairing.face⁻¹).injective hh)

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
