import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryList
import OAI.Geometry.HyperbolicGroups.BoundaryFold

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]

lemma bypassPair_consecutive (f : Perm D) {a b x : D} (ha : x ≠ a) (hb : x ≠ b)
    (hab : a ≠ b) (hn : f a = b) :
    bypassPair f a b x = if f x = a then f b else f x := by
  rw [bypassPair,bypass_away _ _ _ hb,bypass_away _ _ _ ha]
  by_cases he : f x = a
  · have hf : f b ≠ a := fun h => hb (f.injective (he.trans h.symm))
    rw [ite_eq_left he,hn,ite_eq_left rfl,bypass_away _ _ _ hab.symm,ite_eq_right hf,ite_eq_left he]
  · have hf : f x ≠ b := fun h => ha (f.injective (h.trans hn.symm))
    rw [ite_eq_right he,ite_eq_right hf,ite_eq_right he]

namespace IsBoundary
variable {f : Perm D} {xs : List D} (h : IsBoundary f xs)
include h

lemma lift {p : D → Prop} (hp : ∀ x ∈ xs, p x) (g : Perm {x // p x})
    (hg : ∀ x (hx : x ∈ xs), (g ⟨x,hp x hx⟩).val = f x) :
    IsBoundary g (xs.attachWith p hp) := by
  let ys := xs.attachWith p hp
  have hm : ys.map Subtype.val = xs := by
    simpa only [List.map_id_fun,id_eq] using (List.attachWith_map_val (f := id) hp)
  have hnodup : (ys.map Subtype.val).Nodup := by rw [hm]; exact h.nodup
  refine ⟨(List.nodup_map_iff Subtype.val_injective).mp hnodup,?_⟩
  intro x hx
  have hx' : x.val ∈ xs := (List.mem_attachWith hp x).mp hx
  apply Subtype.ext
  have hh := formPerm_map_apply Subtype.val Subtype.val_injective ys x
  rw [hm] at hh
  exact (hg x.val hx').trans ((h.turn x.val hx').trans hh)

omit h in
lemma middle_next {l r : List D} {a b : D} (h : IsBoundary f (l++a::b::r)) : f a = b := by
  have hr : (l++a::b::r) ~r (a::b::(r++l)) := by
    simpa using (List.isRotated_append : (l++a::b::r) ~r ((a::b::r)++l))
  rw [h.turn a (by simp),List.formPerm_eq_of_isRotated h.nodup hr]
  exact List.formPerm_apply_head a b (r++l) (hr.nodup_iff.mp h.nodup)

omit h [DecidableEq D] in
lemma middle_offpair {l r : List D} {a b : D} (hn : (l++a::b::r).Nodup) :
    ∀ x ∈ l++r, OffPair a b x := by
  have hh := List.nodup_append.mp hn
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact ⟨hh.2.2 x hx a (by simp),hh.2.2 x hx b (by simp)⟩
  · have ha := (List.nodup_cons.mp hh.2.1).1
    have hb := (List.nodup_cons.mp (List.nodup_cons.mp hh.2.1).2).1
    exact ⟨fun he => ha (by simp [← he,hx]),fun he => hb (he ▸ hx)⟩

omit h in
lemma erase_middle {l r : List D} {a b : D} (h : IsBoundary f (l++a::b::r)) :
    IsBoundary (bypassPair f a b) (l++r) := by
  have ho := middle_offpair h.nodup
  have hn := List.nodup_append.mp h.nodup
  have ht : (a::b::r).Nodup := hn.2.1
  have hab : a ≠ b := by
    intro he
    exact (List.nodup_cons.mp ht).1 (by simp [he])
  have hp : (l++a::b::r).formPerm a = b := by
    rw [← h.turn a (by simp)]
    exact h.middle_next
  refine ⟨List.nodup_append.mpr ⟨hn.1,ht.of_cons.of_cons,?_⟩,?_⟩
  · intro x hx y hy
    exact hn.2.2 x hx y (by simp [hy])
  · intro x hx
    have ix : x ∈ l++a::b::r := by
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · simp [hx]
    rw [← bypassPair_formPerm l r a b h.nodup]
    rw [bypassPair_consecutive f (ho x hx).1 (ho x hx).2 hab h.middle_next,
      bypassPair_consecutive _ (ho x hx).1 (ho x hx).2 hab hp,
      h.turn x ix,h.turn b (by simp)]

end IsBoundary

namespace PictureMap
variable (M : PictureMap D) {l r : List D} {a b : D}

/-- The free fold deletes exactly the two consecutive entries of the literal
outside word; no cyclic rotation or word-equality surrogate is used. -/
theorem boundaryFold_boundary (h : IsBoundary M.face (l++a::b::r)) (hab : a ≠ b) :
    IsBoundary (M.boundaryFold hab h.middle_next).face
      ((l++r).attachWith (OffPair a b) (IsBoundary.middle_offpair h.nodup)) := by
  apply h.erase_middle.lift
  intro x hx
  exact congrArg Subtype.val (M.boundaryFold_face hab h.middle_next _)

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
