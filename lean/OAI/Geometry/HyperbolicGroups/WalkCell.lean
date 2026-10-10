import Mathlib
import OAI.Geometry.HyperbolicGroups.FaceWalk
import OAI.Geometry.HyperbolicGroups.PictureMap

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r

/-- Indexed oriented steps in polygonal cells, with selected cells permitted
to have arbitrary closed template walks. In the cone target these are precisely
top-cone walks; all fan triangles and decoration disks are frozen. Template
vertices retain their occurrence index, while `vertex` is their actual image
in the target one-skeleton. These are incidence definitions, not diagram or
normal-form hypotheses. -/
structure WalkCellTarget (S : Type v) (C : Type w) (W : Type z) (L : Type k)
    (V : Type t) (A : Type r) [AddCommMonoid A] where
  kind : S → C
  free : C → Bool
  front : S → W
  back : S → W
  vertex : W → V
  label : S → L
  start : L → V
  rev : L → L
  rev_rev : ∀ l, rev (rev l) = l
  front_label : ∀ s, start (label s) = vertex (front s)
  back_label : ∀ s, start (rev (label s)) = vertex (back s)
  opposite : S → S
  opposite_kind : ∀ s, kind (opposite s) = kind s
  opposite_front : ∀ s, front (opposite s) = back s
  opposite_back : ∀ s, back (opposite s) = front s
  opposite_label : ∀ s, label (opposite s) = rev (label s)
  loopless : ∀ s, free (kind s) = true → front s ≠ back s
  simple : ∀ s t, free (kind s) = true → kind s = kind t →
    front s = front t → back s = back t → s = t
  weight : S → A
  opposite_weight : ∀ s, free (kind s) = true → weight s + weight (opposite s) = 0

variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]

structure WalkPicture (T : WalkCellTarget S C W L V A) where
  Dart : Type u
  [finite : Fintype Dart]
  [decEq : DecidableEq Dart]
  pairing : PictureMap Dart
  index : Dart → S
  closed : pairing.FaceClosed (T.front ∘ index) (T.back ∘ index)
  kind : pairing.FaceKind (T.kind ∘ index)
  paired : ∀ x, T.label (index (pairing.edge x)) = T.rev (T.label (index x))
  genusZero : pairing.GenusZero
attribute [instance] WalkPicture.finite WalkPicture.decEq

namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

def chain : A := ∑ x : P.Dart, T.weight (P.index x)
def Simple : Prop := ∀ a b, T.free (T.kind (P.index a)) = true →
  P.pairing.face.SameCycle a b → T.back (P.index a) = T.back (P.index b) → a = b
def NoBigon : Prop := ∀ a, T.free (T.kind (P.index a)) = true →
  P.pairing.face (P.pairing.face a) ≠ a
def Reduced : Prop := ∀ a, T.free (T.kind (P.index a)) = true →
  P.index (P.pairing.edge a) ≠ T.opposite (P.index a)

/-- Retain every individual surviving step and EVERY frozen face. Only free
cone steps may disappear; on frozen faces the original cyclic indexing is
retained exactly, not just up to a word or a chain class. -/
structure Retains (Q : WalkPicture.{u} T) where
  map : Q.Dart → P.Dart
  injective : Function.Injective map
  index : ∀ x, Q.index x = P.index (map x)
  face : ∀ x, T.free (T.kind (Q.index x)) = false →
    map (Q.pairing.face x) = P.pairing.face (map x)
  complete : ∀ x, T.free (T.kind (P.index x)) = false → ∃ y, map y = x

def Retains.refl : P.Retains P :=
  ⟨id,Function.injective_id,fun _ => rfl,fun _ _ => rfl,fun x _ => ⟨x,rfl⟩⟩

def Retains.trans {Q R : WalkPicture.{u} T} (hPQ : P.Retains Q) (hQR : Q.Retains R) :
    P.Retains R := by
  refine ⟨hPQ.map ∘ hQR.map,hPQ.injective.comp hQR.injective,?_,?_,?_⟩
  · intro x; exact (hQR.index x).trans (hPQ.index (hQR.map x))
  · intro x hx
    change hPQ.map (hQR.map (R.pairing.face x)) = _
    rw [hQR.face x hx]
    exact hPQ.face (hQR.map x) (by rw [← hQR.index]; exact hx)
  · intro x hx
    obtain ⟨y,hy⟩ := hPQ.complete x hx
    obtain ⟨z,hz⟩ := hQR.complete y (by rw [hPQ.index,hy]; exact hx)
    exact ⟨z,by simp only [Function.comp_apply,hz,hy]⟩

lemma respects : P.pairing.Respects (T.label ∘ P.index) T.start T.rev := by
  constructor
  · intro x
    change T.start (T.label (P.index (P.pairing.face (P.pairing.edge x)))) = _
    have hc := P.closed (P.pairing.edge x)
    dsimp only [Function.comp_apply] at hc
    rw [T.front_label,hc,← T.back_label,P.paired,T.rev_rev]
    rfl
  · exact P.paired

lemma nonmonogon {x : P.Dart} (hx : T.free (T.kind (P.index x)) = true) :
    P.pairing.face x ≠ x := by
  intro he
  have hc := P.closed x
  change T.front (P.index (P.pairing.face x)) = T.back (P.index x) at hc
  rw [he] at hc
  exact T.loopless (P.index x) hx hc

lemma free_face {x : P.Dart} (hx : T.free (T.kind (P.index x)) = true) :
    T.free (T.kind (P.index (P.pairing.face x))) = true := by
  change T.free ((T.kind ∘ P.index) (P.pairing.face x)) = true
  rw [P.kind]; exact hx

lemma bigon_opposite {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (h₂ : P.pairing.face (P.pairing.face a) = a) :
    P.index (P.pairing.face a) = T.opposite (P.index a) := by
  apply T.simple _ _ (P.free_face ha)
  · exact (P.kind a).trans (T.opposite_kind (P.index a)).symm
  · exact (P.closed a).trans (T.opposite_front (P.index a)).symm
  · have hc := P.closed (P.pairing.face a)
    dsimp only [Function.comp_apply] at hc
    rw [← hc,h₂,T.opposite_back]

/-- The finite splitting producer acts on template vertices, NOT quotient
letter vertices. Consequently a top can never acquire a false repeated
visit merely because several numerical generator labels coincide. -/
theorem makeSimple : ∃ Q : WalkPicture.{u} T,
    Nonempty (P.Retains Q) ∧ Q.Simple ∧ Q.chain = P.chain := by
  obtain ⟨N,hE,hG,hC,hK,hF,hS⟩ := P.pairing.normalize_simple_faces P.genusZero
    (T.front ∘ P.index) (T.back ∘ P.index) P.closed (T.kind ∘ P.index) P.kind T.free
  let Q : WalkPicture.{u} T := {
    Dart := P.Dart
    pairing := N
    index := P.index
    closed := hC
    kind := hK
    paired := by intro x; rw [hE]; exact P.paired x
    genusZero := hG }
  exact ⟨Q,⟨⟨id,Function.injective_id,fun _ => rfl,hF,fun x _ => ⟨x,rfl⟩⟩⟩,hS,rfl⟩

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
