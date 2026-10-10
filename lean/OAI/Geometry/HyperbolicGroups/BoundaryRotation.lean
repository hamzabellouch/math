import Mathlib
import OAI.Geometry.HyperbolicGroups.WordPictureFold

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
variable {D : Type*} [DecidableEq D]
lemma IsBoundary.rotate_append {p : Perm D} {l r : List D}
    (h : IsBoundary p (l++r)) : IsBoundary p (r++l) := by
  simpa only [List.rotate_append_length_eq] using h.rotate l.length

lemma IsBoundary.adjacent_rotate {p : Perm D} {xs : List D} (h : IsBoundary p xs)
    {a b : D} (ha : a ∈ xs) (hab : a ≠ b) (hp : p a = b) :
    ∃ k < xs.length, ∃ z, xs.rotate k = a::b::z := by
  obtain ⟨l,r,he⟩ := List.mem_iff_append.mp ha
  have hb : IsBoundary p ((a::r)++l) := (he ▸ h).rotate_append
  have hlen : r++l ≠ [] := by
    intro hn
    have hc := hb.turn a (by simp)
    rw [List.cons_append,hn,List.formPerm_singleton,one_apply,hp] at hc
    exact hab hc.symm
  obtain ⟨c,z,hz⟩ : ∃ c z, r++l = c::z := List.exists_cons_of_ne_nil hlen
  have hc := hb.turn a (by simp)
  rw [List.cons_append,hz,List.formPerm_apply_head _ _ _ (by simpa only [List.cons_append,hz] using hb.nodup),hp] at hc
  refine ⟨l.length,by simp [he],z,?_⟩
  rw [he,List.rotate_append_length_eq,List.cons_append,hz,hc]

end HyperbolicObstruction.PictureSwitch

namespace HyperbolicObstruction.WordPictures
namespace Homotopy
variable {A : Type*} {R : Set (Word A)} {u v : Word A} {k : ℕ}
/-- Moving the boundary basepoint is area-free for a null word; it is not
asserted that a cyclic shift represents the same free-group element. -/
lemma rotate_null (h : Homotopy R (v++u) [] k) : Homotopy R (u++v) [] k := by
  have hf : FreeGroup.mk (u++v) = FreeGroup.mk (u++(v++u)++FreeGroup.invRev u) := by
    simp only [← FreeGroup.mul_mk,← FreeGroup.inv_mk]
    group
  simpa only [Nat.zero_add] using (Homotopy.free hf).trans (h.conjugate u)
lemma unrotate_null {w : Word A} (i : ℕ) (hi : i ≤ w.length)
    (h : Homotopy R (w.rotate i) [] k) : Homotopy R w [] k := by
  rw [List.rotate_eq_drop_append_take hi] at h
  simpa only [List.take_append_drop] using h.rotate_null
end Homotopy

namespace WordPicture
open HyperbolicObstruction.PictureSwitch
variable {A : Type*} {R : Set (Word A)} {w : Word A}
variable (P : WordPicture R w)

lemma all_outside_rotate (h : ∀ x, x ∈ P.outside) (k : ℕ) :
    ∀ x, x ∈ (P.rotate k).outside := fun x => List.mem_rotate.mpr (h x)

lemma all_outside_fold {l r : List P.Dart} {a b : P.Dart}
    (he : P.outside = l++a::b::r) (hc : P.label a = invLetter (P.label b))
    (h : ∀ x, x ∈ P.outside) : ∀ x, x ∈ (P.foldAt he hc).outside := by
  intro x
  change x ∈ (l++r).attachWith (OffPair a b) _
  apply (List.mem_attachWith _ x).mpr
  have hx := h x.val
  rw [he] at hx
  simp only [List.mem_append,List.mem_cons] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl hx
  · rcases hx with ha | hb | hx
    · exact False.elim (x.property.1 ha)
    · exact False.elim (x.property.2 hb)
    · exact Or.inr hx

end WordPicture
end HyperbolicObstruction.WordPictures
end
end

section

end
end

end OAI
