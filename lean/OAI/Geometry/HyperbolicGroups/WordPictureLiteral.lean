import Mathlib
import OAI.Geometry.HyperbolicGroups.WordPictureExist
import OAI.Geometry.HyperbolicGroups.WordPictureFold

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)} {w v : Word A}
namespace WordPicture

/-- Inserting a freely canceling pair is attaching a thickened edge at the
specified exterior corner, including the formerly empty exterior. -/
def insertAt (P : WordPicture R w) {l r : Word A} (he : w = l++r) (a : A × Bool) :
    WordPicture R (l++a::invLetter a::r) := by
  have P' := P.rotate l.length
  have he' : w.rotate l.length = r++l := by rw [he,List.rotate_append_length_eq]
  rw [he'] at P'
  have Q := (P'.append (freePair R a)).rotate r.length
  have he'' : ((r++l)++[a,invLetter a]).rotate r.length = l++a::invLetter a::r := by
    rw [List.append_assoc,List.rotate_append_length_eq]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  exact he'' ▸ Q

lemma of_reverse_step (P : WordPicture R v) (h : FreeGroup.Red.Step w v) :
    Nonempty (WordPicture R w) := by
  cases h with
  | @not l r x b => exact ⟨P.insertAt rfl (x,b)⟩

lemma of_reverse_red (h : FreeGroup.Red w v) :
    Nonempty (WordPicture R v) → Nonempty (WordPicture R w) := by
  induction h with
  | refl => exact id
  | tail h h' ih => rintro ⟨P⟩; exact ih (P.of_reverse_step h')

lemma of_free_eq (P : WordPicture R w) (he : FreeGroup.mk w = FreeGroup.mk v) :
    Nonempty (WordPicture R v) := by
  obtain ⟨z,hw,hv⟩ := FreeGroup.Red.exact.mp he
  exact of_reverse_red hv (P.of_red hw)

end WordPicture

/-- Literal van Kampen disk realization from the ordinary presented group.
All sides and relator boundaries are indexed; the map is genuinely finite
and genus zero. There is no disk realization, area bound, or planarity premise.
This producer handles arbitrary (not just reduced or nonempty) null words. -/
theorem literal_picture_existence {R : Set (Word A)} (w : Word A)
    (h : PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk w) = 1) :
    Nonempty (WordPicture R w) := by
  obtain ⟨v,hv,⟨P⟩⟩ := picture_existence w h
  exact P.of_free_eq hv

end HyperbolicObstruction.WordPictures
end
end

section

end
end

end OAI
