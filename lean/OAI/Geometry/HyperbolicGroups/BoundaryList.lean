import Mathlib
import OAI.Geometry.HyperbolicGroups.IndexedFace
import OAI.Geometry.HyperbolicGroups.PermErasePair

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]

lemma bypass_formPerm_head (a : D) (xs : List D) (hn : (a::xs).Nodup) :
    bypass (a::xs).formPerm a = xs.formPerm := by
  cases xs with
  | nil => simp [bypass]; rfl
  | cons b xs =>
    rw [bypass,List.formPerm_apply_head _ _ _ hn,List.formPerm_cons_cons]
    rw [← mul_assoc,swap_mul_self,one_mul]

lemma bypassPair_formPerm_head (a b : D) (xs : List D) (hn : (a::b::xs).Nodup) :
    bypassPair (a::b::xs).formPerm a b = xs.formPerm := by
  rw [bypassPair,bypass_formPerm_head _ _ hn,bypass_formPerm_head _ _ hn.of_cons]

lemma bypassPair_formPerm (l r : List D) (a b : D) (hn : (l++a::b::r).Nodup) :
    bypassPair (l++a::b::r).formPerm a b = (l++r).formPerm := by
  have hr : (l++a::b::r) ~r (a::b::(r++l)) := by
    simpa using (List.isRotated_append : (l++a::b::r) ~r ((a::b::r)++l))
  have hn' : (a::b::(r++l)).Nodup := hr.nodup_iff.mp hn
  rw [List.formPerm_eq_of_isRotated hn hr,bypassPair_formPerm_head _ _ _ hn']
  exact List.formPerm_eq_of_isRotated hn'.of_cons.of_cons List.isRotated_append

/-- An enumerated literal face boundary; the empty outside is allowed. -/
structure IsBoundary (f : Perm D) (xs : List D) : Prop where
  nodup : xs.Nodup
  turn : ∀ x ∈ xs, f x = xs.formPerm x

lemma formPerm_map_apply {E : Type*} [DecidableEq E] (j : D → E)
    (hj : Function.Injective j) (xs : List D) (x : D) :
    (xs.map j).formPerm (j x) = j (xs.formPerm x) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      simp only [List.map_cons,List.formPerm_cons_cons,mul_apply] at ih ⊢
      rw [ih,← hj.map_swap]

namespace IsBoundary
variable {f : Perm D} {xs : List D} (h : IsBoundary f xs)
include h

lemma invariant {x : D} (hx : x ∈ xs) : f x ∈ xs := by
  rw [h.turn x hx]
  exact List.formPerm_apply_mem_of_mem hx

lemma iterate {x : D} (hx : x ∈ xs) (k : ℕ) :
    (f^k) x = (xs.formPerm^k) x := by
  have hk : ∀ i : ℕ, (xs.formPerm^i) x ∈ xs := by
    intro i
    induction i with
    | zero => exact hx
    | succ i ih =>
      rw [pow_succ',mul_apply]
      exact List.formPerm_apply_mem_of_mem ih
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',mul_apply,ih,h.turn _ (hk k),pow_succ',mul_apply]

lemma sameCycle {x y : D} (hx : x ∈ xs) (hy : y ∈ xs) : f.SameCycle x y := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hy
  have h0 : 0 < xs.length := by omega
  have hs : ∀ j (hj : j < xs.length), f.SameCycle xs[0] xs[j] := by
    intro j hj
    have he : (f^j) xs[0] = xs[j] := by
      rw [h.iterate (List.getElem_mem h0),List.formPerm_pow_apply_getElem _ h.nodup]
      simp only [Nat.zero_add,Nat.mod_eq_of_lt hj]
    exact he ▸ (SameCycle.rfl (f := f) (x := xs[0])).pow_right
  exact (hs i hi).symm.trans (hs j hj)

lemma mem_of_sameCycle {x y : D} (hx : x ∈ xs) (hxy : f.SameCycle x y) : y ∈ xs := by
  have hinv : ∀ z, f z ∈ xs ↔ z ∈ xs := by
    intro z
    constructor
    · intro hz
      have hh : xs.formPerm⁻¹ (f z) ∈ xs := by
        apply List.mem_of_formPerm_apply_mem
        simpa only [Perm.inv_def,Equiv.apply_symm_apply] using hz
      have he := h.turn _ hh
      simp only [Perm.inv_def,Equiv.apply_symm_apply] at he
      have he' : xs.formPerm⁻¹ (f z) = z := f.injective he
      rwa [he'] at hh
    · exact h.invariant
  obtain ⟨k,rfl⟩ := hxy
  have hmap : ∀ z, decide (f z ∈ xs) = decide (z ∈ xs) := fun z => by simp only [hinv z]
  have he := semiconj_perm_zpow (t := (1 : Perm Bool)) (j := fun z => decide (z ∈ xs)) hmap k x
  simpa only [one_zpow,one_apply,show decide (x ∈ xs) = true from decide_eq_true hx,decide_eq_true_eq] using he

lemma disjoint {ys : List D} (hg : IsBoundary f ys) {x y : D}
    (hx : x ∈ xs) (hy : y ∈ ys) (hne : ¬ f.SameCycle x y) :
    ∀ z ∈ xs, z ∉ ys := by
  intro z hz hzy
  exact hne ((h.sameCycle hx hz).trans (hg.sameCycle hzy hy))

lemma map {E : Type*} [DecidableEq E] {g : Perm E} (j : D → E)
    (hj : Function.Injective j) (hc : ∀ x, j (f x) = g (j x)) :
    IsBoundary g (xs.map j) := by
  refine ⟨h.nodup.map hj,?_⟩
  intro y hy
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
  rw [← hc,h.turn x hx,formPerm_map_apply j hj]

end IsBoundary
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
