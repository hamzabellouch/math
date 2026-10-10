import Mathlib

namespace OAI

section
section


/-! Algebraic van Kampen existence, with actual words and area-counted local
moves (not a finiteness or isoperimetric assumption). Free cancellation has
zero cost; each orientation of a listed relator disk has cost one. -/
noncomputable section
namespace HyperbolicObstruction.WordPictures

variable {A : Type*}
abbrev Word (A : Type*) := List (A × Bool)

inductive Move (R : Set (Word A)) : Word A → Word A → ℕ → Prop
  | free {u v} : FreeGroup.Red.Step u v → Move R u v 0
  | face (l r w) (h : w ∈ R) : Move R (l ++ w ++ r) (l ++ r) 1
  | reverseFace (l r w) (h : w ∈ R) :
      Move R (l ++ FreeGroup.invRev w ++ r) (l ++ r) 1

inductive Homotopy (R : Set (Word A)) : Word A → Word A → ℕ → Prop
  | refl (w) : Homotopy R w w 0
  | move {u v n} : Move R u v n → Homotopy R u v n
  | symm {u v n} : Homotopy R u v n → Homotopy R v u n
  | trans {u v w m n} : Homotopy R u v m → Homotopy R v w n → Homotopy R u w (m+n)

namespace Move
variable {R : Set (Word A)} {u v : Word A} {n : ℕ}
lemma contextual (h : Move R u v n) (l r : Word A) :
    Move R (l ++ u ++ r) (l ++ v ++ r) n := by
  cases h with
  | free h => exact free (h.append_left.append_right)
  | face l' r' w h => simpa only [List.append_assoc] using face (l++l') (r'++r) w h
  | reverseFace l' r' w h =>
      simpa only [List.append_assoc] using reverseFace (l++l') (r'++r) w h

lemma reverse (h : Move R u v n) : Move R (FreeGroup.invRev u) (FreeGroup.invRev v) n := by
  cases h with
  | free h => exact free h.invRev
  | face l r w h =>
    simpa only [FreeGroup.invRev_append,List.append_assoc] using
      reverseFace (FreeGroup.invRev r) (FreeGroup.invRev l) w h
  | reverseFace l r w h =>
    simpa only [FreeGroup.invRev_append,FreeGroup.invRev_invRev,List.append_assoc] using
      face (FreeGroup.invRev r) (FreeGroup.invRev l) w h
end Move

namespace Homotopy
variable {R : Set (Word A)} {u v w : Word A} {n : ℕ}
lemma contextual (h : Homotopy R u v n) (l r : Word A) :
    Homotopy R (l ++ u ++ r) (l ++ v ++ r) n := by
  induction h with
  | refl => exact refl _
  | move h => exact move (h.contextual l r)
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'
lemma reverse (h : Homotopy R u v n) :
    Homotopy R (FreeGroup.invRev u) (FreeGroup.invRev v) n := by
  induction h with
  | refl => exact refl _
  | move h => exact move h.reverse
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'

lemma of_reduction (h : FreeGroup.Red u v) : Homotopy R u v 0 := by
  induction h with
  | refl => exact refl _
  | tail h h' ih => simpa using ih.trans (move (.free h'))

/-- Equality in the free group uses only free folds, not a face relator. -/
lemma free (h : FreeGroup.mk u = FreeGroup.mk v) : Homotopy R u v 0 := by
  obtain ⟨z,hz,hz'⟩ := FreeGroup.Red.exact.mp h
  simpa using (of_reduction hz).trans (of_reduction hz').symm

lemma append {m : ℕ} (h : Homotopy R u v n) (h' : Homotopy R w [] m) :
    Homotopy R (u++w) v (n+m) := by
  have h1 : Homotopy R (u++w) (v++w) n := by
    simpa using h.contextual [] w
  have h2 : Homotopy R (v++w) v m := by
    simpa using h'.contextual v []
  exact h1.trans h2

lemma append_null {v : Word A} {m : ℕ} (h : Homotopy R u [] n)
    (h' : Homotopy R v [] m) : Homotopy R (u++v) [] (n+m) := h.append h'

lemma conjugate (h : Homotopy R u [] n) (q : Word A) :
    Homotopy R (q++u++FreeGroup.invRev q) [] n := by
  have h1 : Homotopy R (q++u++FreeGroup.invRev q) (q++FreeGroup.invRev q) n := by
    simpa using h.contextual q (FreeGroup.invRev q)
  have h2 : Homotopy R (q++FreeGroup.invRev q) [] 0 := free (by
    rw [← FreeGroup.mul_mk,← FreeGroup.inv_mk,← FreeGroup.one_eq_mk,mul_inv_cancel])
  simpa using h1.trans h2
end Homotopy

/-- Freely represented words admitting a finite disk construction. -/
def nullSubgroup (R : Set (Word A)) : Subgroup (FreeGroup A) where
  carrier g := ∃ w, FreeGroup.mk w = g ∧ ∃ n, Homotopy R w [] n
  one_mem' := ⟨[],rfl,0,.refl _⟩
  mul_mem' := by
    rintro _ _ ⟨u,rfl,m,hu⟩ ⟨v,rfl,n,hv⟩
    exact ⟨u++v,rfl,m+n,hu.append_null hv⟩
  inv_mem' := by
    rintro _ ⟨u,rfl,n,hu⟩
    exact ⟨FreeGroup.invRev u,rfl,n,by simpa using hu.reverse⟩

instance (R : Set (Word A)) : (nullSubgroup R).Normal where
  conj_mem := by
    rintro _ ⟨u,rfl,n,hu⟩ g
    obtain ⟨q,rfl⟩ := Quot.exists_rep g
    exact ⟨q++u++FreeGroup.invRev q,rfl,n,hu.conjugate q⟩

lemma relators_in_null (R : Set (Word A)) : FreeGroup.mk '' R ⊆ nullSubgroup R := by
  rintro _ ⟨w,hw,rfl⟩
  exact ⟨w,rfl,1,by simpa using (Homotopy.move (Move.face [] [] w hw))⟩

/-- Null words in the ordinary presented group have a finite area-counted
word disk. No boundedness, reducedness or planarity premise is required. -/
theorem existence {R : Set (Word A)} (w : Word A)
    (h : PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk w) = 1) :
    ∃ n, Homotopy R w [] n := by
  have hg := PresentedGroup.mk_eq_one_iff.mp h
  have hh := (Subgroup.normalClosure_le_normal (relators_in_null R)) hg
  obtain ⟨v,he,n,hv⟩ := hh
  exact ⟨n,by simpa using (Homotopy.free he.symm).trans hv⟩

lemma move_sound {R : Set (Word A)} {u v : Word A} {n : ℕ} (h : Move R u v n) :
    PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk u) =
      PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk v) := by
  let f := PresentedGroup.mk (FreeGroup.mk '' R)
  cases h with
  | free h => exact congrArg f (Quot.sound h)
  | face l r w h =>
    have hw : f (FreeGroup.mk w) = 1 := PresentedGroup.one_of_mem ⟨w,h,rfl⟩
    change f _ = f _
    simp only [← FreeGroup.mul_mk,map_mul,hw,mul_one]
  | reverseFace l r w h =>
    have hw : f (FreeGroup.mk w) = 1 := PresentedGroup.one_of_mem ⟨w,h,rfl⟩
    change f _ = f _
    simp only [← FreeGroup.mul_mk,← FreeGroup.inv_mk,map_mul,map_inv,hw,inv_one,mul_one]

lemma sound {R : Set (Word A)} {u v : Word A} {n : ℕ} (h : Homotopy R u v n) :
    PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk u) =
      PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk v) := by
  induction h with
  | refl => rfl
  | move h => exact move_sound h
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'

end HyperbolicObstruction.WordPictures
end
end

section

end
end

end OAI
