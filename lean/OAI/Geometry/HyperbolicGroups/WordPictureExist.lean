import Mathlib
import OAI.Geometry.HyperbolicGroups.WordPictureBase
import OAI.Geometry.HyperbolicGroups.WordPictureAppend

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace IsBoundary
variable {D : Type*} [DecidableEq D] {f : Perm D} {xs : List D}
lemma rotate (h : IsBoundary f xs) (n : ℕ) : IsBoundary f (xs.rotate n) := by
  refine ⟨by simpa using h.nodup,?_⟩
  intro x hx
  rw [List.formPerm_rotate _ h.nodup]
  exact h.turn x (List.mem_rotate.mp hx)
end IsBoundary
end HyperbolicObstruction.PictureSwitch

namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)} {w : Word A}
namespace WordPicture
variable (P : WordPicture R w)

def rotate (n : ℕ) : WordPicture R (w.rotate n) where
  Dart := P.Dart
  pairing := P.pairing
  genusZero := P.genusZero
  label := P.label
  paired := P.paired
  outside := P.outside.rotate n
  boundary := P.boundary.rotate n
  word := by rw [List.map_rotate,P.word]
  interior := by intro x hx; exact P.interior x (by simpa using hx)

def conjugateLetter (a : A × Bool) : WordPicture R (a::(w++[invLetter a])) := by
  have P' := (P.append (freePair R (invLetter a))).rotate (w.length+1)
  have he : (w++[invLetter a,invLetter (invLetter a)]).rotate (w.length+1) =
      a::(w++[invLetter a]) := by
    rw [invLetter_invLetter]
    have hh := List.rotate_append_length_eq (w++[invLetter a]) [a]
    simpa only [List.append_assoc,List.singleton_append,List.length_append,List.length_singleton] using hh
  rw [he] at P'
  exact P'

def conjugate (q : Word A) : WordPicture R (q++w++FreeGroup.invRev q) := by
  induction q with
  | nil => simpa using P
  | cons a q ih =>
    have h := ih.conjugateLetter a
    rw [FreeGroup.invRev_cons,show FreeGroup.invRev [a] = [invLetter a] from rfl]
    simpa only [List.cons_append,List.append_assoc] using h
end WordPicture

/-- Elements represented by actual finite genus-zero diagrams. The subgroup
and its normality are proved by gluing, reflecting and attaching a whisker. -/
def pictureSubgroup (R : Set (Word A)) : Subgroup (FreeGroup A) where
  carrier g := ∃ w, FreeGroup.mk w = g ∧ Nonempty (WordPicture R w)
  one_mem' := ⟨[],rfl,⟨WordPicture.empty R⟩⟩
  mul_mem' := by
    rintro _ _ ⟨u,rfl,⟨P⟩⟩ ⟨v,rfl,⟨Q⟩⟩
    exact ⟨u++v,rfl,⟨P.append Q⟩⟩
  inv_mem' := by
    rintro _ ⟨u,rfl,⟨P⟩⟩
    exact ⟨FreeGroup.invRev u,rfl,⟨P.mirror⟩⟩

instance (R : Set (Word A)) : (pictureSubgroup R).Normal where
  conj_mem := by
    rintro _ ⟨u,rfl,⟨P⟩⟩ g
    obtain ⟨q,rfl⟩ := Quot.exists_rep g
    exact ⟨q++u++FreeGroup.invRev q,rfl,⟨P.conjugate q⟩⟩

/-- Van Kampen realization at the freely represented boundary level: every
null element has an actual finite genus-zero side-pairing with only the
specified relator faces. The next literal-boundary step is free folding. -/
theorem picture_existence {R : Set (Word A)} (w : Word A)
    (h : PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk w) = 1) :
    ∃ v, FreeGroup.mk v = FreeGroup.mk w ∧ Nonempty (WordPicture R v) := by
  apply (Subgroup.normalClosure_le_normal (N := pictureSubgroup R) ?_) (PresentedGroup.mk_eq_one_iff.mp h)
  rintro _ ⟨v,hv,rfl⟩
  exact ⟨v,rfl,WordPicture.of_relator hv⟩

end HyperbolicObstruction.WordPictures
end
end

section

end
end

end OAI
