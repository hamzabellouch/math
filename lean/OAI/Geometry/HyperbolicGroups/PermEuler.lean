import Mathlib
import OAI.Geometry.HyperbolicGroups.PermSwitch
import OAI.Geometry.HyperbolicGroups.SetoidGlue

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

omit [DecidableEq D] in
lemma sameCycle_le_of_apply {p : Perm D} {s : Setoid D}
    (h : ∀ x, s x (p x)) : SameCycle.setoid p ≤ s := by
  intro a b hab
  obtain ⟨n,rfl⟩ := hab.exists_nat_pow_eq
  clear hab
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_apply]
    exact s.trans' ih (h _)

lemma sameCycle_swap_le {s : Setoid D} {a b : D} (h : s a b) :
    SameCycle.setoid (swap a b) ≤ s := by
  apply sameCycle_le_of_apply
  intro x
  by_cases ha : x = a
  · subst x; simpa using h
  by_cases hb : x = b
  · subst x; simpa using s.symm' h
  · simp [swap_apply_of_ne_of_ne ha hb]

omit [DecidableEq D] in
lemma sameCycle_mul_le {s : Setoid D} {p q : Perm D}
    (hp : SameCycle.setoid p ≤ s) (hq : SameCycle.setoid q ≤ s) :
    SameCycle.setoid (p*q) ≤ s := by
  apply sameCycle_le_of_apply
  intro x
  exact s.trans' (hq (SameCycle.rfl.apply_right)) (hp (SameCycle.rfl.apply_right))

lemma sameCycle_glue {p : Perm D} {s : Setoid D} (h : SameCycle.setoid p ≤ s) (a b : D) :
    SameCycle.setoid (p * swap a b) ≤ glue s a b :=
  sameCycle_mul_le (h.trans (le_glue s a b)) (sameCycle_swap_le (glue_pair s a b))

/-- The Euler potential increases by at most one on adjoining a paired side.
If the side joins different components, the face cycles merge and the bound
is an equality. This is the combinatorial source of the genus inequality. -/
lemma potential_step {p : Perm D} {s : Setoid D} (h : SameCycle.setoid p ≤ s)
    (a b : D) :
    cycles (p * swap a b) - 2 * (Nat.card (Quotient (glue s a b)) : ℤ) ≤
      cycles p - 2 * (Nat.card (Quotient s) : ℤ) + 1 := by
  rw [card_glue]
  by_cases hs : s a b
  · rw [ite_eq_left hs,sub_zero]
    by_cases hab : a = b
    · subst b
      have he : swap a a = (1 : Perm D) := swap_self a
      rw [he,mul_one]
      omega
    by_cases hp : p.SameCycle a b
    · rw [cycles_split_right p hab hp]
      omega
    · have hc := cycles_merge_right p hp
      omega
  · rw [ite_eq_right hs]
    have hp : ¬ p.SameCycle a b := fun hp => hs (h hp)
    have hc := cycles_merge_right p hp
    omega

/-- Components after adjoining a finite list of side pairings. -/
def joins (s : Setoid D) : List (D × D) → Setoid D
  | [] => s
  | (a,b)::l => joins (glue s a b) l

def swaps (l : List (D × D)) : Perm D := (l.map (fun ab => swap ab.1 ab.2)).prod

omit [DecidableEq D] [Fintype D] in
lemma le_joins (s : Setoid D) (l : List (D × D)) : s ≤ joins s l := by
  induction l generalizing s with
  | nil => exact le_rfl
  | cons ab l ih => exact (le_glue s ab.1 ab.2).trans (ih _)

omit [DecidableEq D] [Fintype D] in
lemma joins_le (s t : Setoid D) (l : List (D × D)) (hs : s ≤ t)
    (hl : ∀ ab ∈ l, t ab.1 ab.2) : joins s l ≤ t := by
  induction l generalizing s with
  | nil => exact hs
  | cons ab l ih =>
    exact ih _ (glue_le s ab.1 ab.2 hs (hl ab (by simp)))
      (fun cd hc => hl cd (by simp [hc]))

lemma sameCycle_joins {p : Perm D} {s : Setoid D} (h : SameCycle.setoid p ≤ s)
    (l : List (D × D)) : SameCycle.setoid (p * swaps l) ≤ joins s l := by
  induction l generalizing p s with
  | nil => simpa [swaps,joins] using h
  | cons ab l ih =>
    simpa [swaps,joins,← mul_assoc] using ih (sameCycle_glue h ab.1 ab.2)

/-- The full finite combinatorial Euler inequality before identifying the
final components with a particular surface. -/
theorem potential_list {p : Perm D} {s : Setoid D} (h : SameCycle.setoid p ≤ s)
    (l : List (D × D)) :
    cycles (p * swaps l) - 2 * (Nat.card (Quotient (joins s l)) : ℤ) ≤
      cycles p - 2 * (Nat.card (Quotient s) : ℤ) + l.length := by
  induction l generalizing p s with
  | nil => simp [swaps,joins]
  | cons ab l ih =>
    have hh := ih (sameCycle_glue h ab.1 ab.2)
    have hs := potential_step h ab.1 ab.2
    simp only [swaps,List.map_cons,List.prod_cons,← mul_assoc,joins] at *
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    omega

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
