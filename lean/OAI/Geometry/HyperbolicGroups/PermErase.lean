import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureRestrict

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]

lemma sameCycle_setoid_merge_left [Fintype D] (p : Perm D) {a b : D}
    (h : ¬ p.SameCycle a b) :
    SameCycle.setoid (swap a b * p) = glue (SameCycle.setoid p) a b := by
  let q := swap a b * p
  have hq : q.SameCycle a b := sameCycle_after_swap p h
  have hle : SameCycle.setoid p ≤ SameCycle.setoid q := by
    apply sameCycle_le_of_apply
    intro x
    have ht : SameCycle.setoid q (q x) (swap a b (q x)) :=
      sameCycle_swap_le hq SameCycle.rfl.apply_right
    have he : swap a b (q x) = p x := by simp [q]
    rw [he] at ht
    exact SameCycle.rfl.apply_right.trans ht
  apply le_antisymm
  · exact sameCycle_mul_le (sameCycle_swap_le (glue_pair _ a b)) (le_glue _ a b)
  · exact glue_le _ a b hle hq

/-- Fix the punctured point and bypass it in its original cycle. Restricting
this permutation to the complement literally erases that indexed corner. -/
def bypass (p : Perm D) (a : D) : Perm D := swap a (p a) * p

@[simp] lemma bypass_fixed (p : Perm D) (a : D) : bypass p a a = a := by
  simp [bypass]

lemma bypass_away (p : Perm D) (a x : D) (hx : x ≠ a) :
    bypass p a x = if p x = a then p a else p x := by
  by_cases he : p x = a
  · simp [bypass,he]
  · simp [bypass,swap_apply_of_ne_of_ne he (p.injective.ne hx),he]

lemma bypass_invariant (p : Perm D) (a x : D) : bypass p a x ≠ a ↔ x ≠ a := by
  have h := (bypass p a).apply_eq_iff_eq (x := x) (y := a)
  rw [bypass_fixed] at h
  exact not_congr h

def erase (p : Perm D) (a : D) : Perm {x : D // x ≠ a} :=
  (bypass p a).subtypePerm (bypass_invariant p a)

variable [Fintype D]

lemma bypass_orbits (p : Perm D) (a x y : D) (hx : x ≠ a) (hy : y ≠ a) :
    (bypass p a).SameCycle x y ↔ p.SameCycle x y := by
  by_cases ha : p a = a
  · simp only [bypass,ha,swap_self,← Equiv.Perm.one_def,one_mul]
  · have hq : ¬ (bypass p a).SameCycle (p a) a := by
      intro h
      exact ha (h.eq_of_right (bypass_fixed p a))
    have hmerge := sameCycle_setoid_merge_left (bypass p a) hq
    have he : swap (p a) a * bypass p a = p := by
      rw [bypass,swap_comm (p a) a,← mul_assoc,swap_mul_self,one_mul]
    rw [he] at hmerge
    have hxa : ¬ (bypass p a).SameCycle x a := fun h => hx (h.eq_of_right (bypass_fixed p a))
    have hya : ¬ (bypass p a).SameCycle y a := fun h => hy (h.eq_of_right (bypass_fixed p a))
    change SameCycle.setoid (bypass p a) x y ↔ SameCycle.setoid p x y
    rw [hmerge,glue_iff]
    have hxq : ¬ (SameCycle.setoid (bypass p a)) x a := hxa
    have hyq : ¬ (SameCycle.setoid (bypass p a)) y a := hya
    simp only [hxq,hyq,ite_false,Quotient.eq]

lemma erase_orbits (p : Perm D) (a : D) (x y : {x : D // x ≠ a}) :
    (erase p a).SameCycle x y ↔ p.SameCycle x.val y.val := by
  rw [erase,sameCycle_subtypePerm]
  exact bypass_orbits p a x.val y.val x.property y.property

lemma bypass_cycles (p : Perm D) (a : D) :
    cycles (bypass p a) = cycles p + if p a = a then 0 else 1 := by
  by_cases h : p a = a
  · simp only [bypass,h,swap_self,← Equiv.Perm.one_def,one_mul,ite_eq_left,add_zero]
  · rw [ite_eq_right h,bypass]
    exact cycles_split p (Ne.symm h) SameCycle.rfl.apply_right

lemma erase_cycles (p : Perm D) (a : D) :
    cycles (erase p a) = cycles p - if p a = a then 1 else 0 := by
  let s := (bypass p a).subtypePerm (p := fun x => ¬ x ≠ a)
    (fun x => not_congr (bypass_invariant p a x))
  have hc : cycles (bypass p a) = cycles (erase p a) + cycles s := by
    simpa only [cycles_eq_card_classes,erase,s] using
      (cycles_subtype_split (P := fun x => x ≠ a) (bypass p a) (bypass_invariant p a))
  have hs : s = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change bypass p a x.val = x.val
    have hx : x.val = a := by simpa using x.property
    rw [hx,bypass_fixed]
  have hsingle : cycles s = 1 := by
    let : Unique {x : D // ¬ x ≠ a} :=
      ⟨⟨a,by simp⟩,fun x => Subtype.ext (by simpa using x.property)⟩
    rw [hs]
    simp [cycles,defect]
  rw [hsingle,bypass_cycles] at hc
  split_ifs at hc ⊢ <;> omega

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
