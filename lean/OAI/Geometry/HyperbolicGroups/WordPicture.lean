import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureEuler
import OAI.Geometry.HyperbolicGroups.PictureMirror
import OAI.Geometry.HyperbolicGroups.WordDisk
import OAI.Geometry.HyperbolicGroups.BoundaryList

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable {A : Type u}

def invLetter (a : A × Bool) : A × Bool := (a.1,!a.2)
@[simp] lemma invLetter_invLetter (a : A × Bool) : invLetter (invLetter a) = a := by
  rcases a with ⟨a,b⟩; cases b <;> rfl

def SymmetricRelator (R : Set (Word A)) (w : Word A) : Prop :=
  w ∈ R ∨ FreeGroup.invRev w ∈ R

lemma symmetricRelator_inv {R : Set (Word A)} {w : Word A} (h : SymmetricRelator R w) :
    SymmetricRelator R (FreeGroup.invRev w) := by
  rcases h with h | h
  · exact Or.inr (by simpa using h)
  · exact Or.inl h

/-- Finite, genuinely genus-zero van Kampen side-pairings, with a literal
outside word and enumerated indexed relator boundaries on every interior
face. There is no disk-existence or isoperimetric field. -/
structure WordPicture (R : Set (Word A)) (w : Word A) where
  Dart : Type
  [finite : Fintype Dart]
  [decEq : DecidableEq Dart]
  pairing : PictureMap Dart
  genusZero : pairing.GenusZero
  label : Dart → A × Bool
  paired : ∀ x, label (pairing.edge x) = invLetter (label x)
  outside : List Dart
  boundary : IsBoundary pairing.face outside
  word : outside.map label = w
  interior : ∀ x, x ∉ outside → ∃ xs : List Dart,
    IsBoundary pairing.face xs ∧ x ∈ xs ∧ SymmetricRelator R (xs.map label)
attribute [instance] WordPicture.finite WordPicture.decEq

namespace WordPicture
variable {R : Set (Word A)} {w : Word A} (P : WordPicture R w)

lemma respects : P.pairing.Respects P.label (fun _ => ()) invLetter :=
  ⟨fun _ => rfl,P.paired⟩

def mirror : WordPicture R (FreeGroup.invRev w) where
  Dart := P.Dart
  pairing := P.pairing.mirror
  genusZero := P.pairing.mirror_genusZero P.genusZero
  label := invLetter ∘ P.label
  paired := fun x => by
    change invLetter (P.label (P.pairing.edge x)) = invLetter (invLetter (P.label x))
    rw [P.paired]
  outside := P.outside.reverse
  boundary := P.boundary.reverse
  word := by
    simp only [List.map_reverse,List.map_map,← P.word,FreeGroup.invRev]
    rfl
  interior := by
    intro x hx
    have hx' : x ∉ P.outside := by simpa using hx
    obtain ⟨xs,hs,hm,hr⟩ := P.interior x hx'
    refine ⟨xs.reverse,hs.reverse,by simpa using hm,?_⟩
    convert symmetricRelator_inv hr using 1
    simp only [List.map_reverse,List.map_map,FreeGroup.invRev]
    rfl

/-- No faces are required to fill the empty word. -/
def empty (R : Set (Word A)) : WordPicture R [] where
  Dart := PEmpty
  pairing := {
    face := 1
    edge := 1
    edge_sq := one_mul _
    edge_ne := fun x => PEmpty.elim x }
  genusZero := by
    simp only [PictureMap.GenusZero,PictureMap.euler,PictureMap.vertex,
      cycles,defect,Fintype.card_pempty,one_mul,support_one,Finset.card_empty,
      cycleType_one,Multiset.card_zero,Nat.cast_zero,sub_zero,add_zero,Int.zero_ediv,
      zero_eq_mul]
    right
    norm_cast
    apply Nat.card_eq_zero.mpr
    exact Or.inl ⟨fun x => Quotient.inductionOn x (fun x => PEmpty.elim x)⟩
  label := PEmpty.elim
  paired := fun x => PEmpty.elim x
  outside := []
  boundary := ⟨by simp,fun _ h => False.elim (List.not_mem_nil h)⟩
  word := rfl
  interior := fun x => PEmpty.elim x

end WordPicture
end HyperbolicObstruction.WordPictures
end
end

section

end
end

end OAI
