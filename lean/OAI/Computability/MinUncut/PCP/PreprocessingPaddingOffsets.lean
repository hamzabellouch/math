import Mathlib
import OAI.Computability.MinUncut.PCP.PreprocessingRegularTables

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingPaddingOffsets

open PreprocessingRegularTables
open scoped BigOperators

private theorem idxOf_map_injective {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (xs : List A) (a : A) :
    (xs.map f).idxOf (f a) = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x = a
    · subst x; simp
    · simp [List.idxOf_cons_ne, h, hf.ne h, ih]

theorem sigma_idxOf {A : Type*} [DecidableEq A] (sizes : A → Nat)
    (xs : List A) (a : A) (ha : a ∈ xs) (j : Fin (sizes a)) :
    (xs.sigma (fun x => List.finRange (sizes x))).idxOf ⟨a, j⟩ =
      ((xs.take (xs.idxOf a)).map sizes).sum + j.val := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.sigma_cons]
    by_cases h : x = a
    · subst x
      have hm : (⟨a, j⟩ : Σ x, Fin (sizes x)) ∈
          (List.finRange (sizes a)).map (Sigma.mk a) := by
        exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
      rw [List.idxOf_append_of_mem hm,
        idxOf_map_injective (Sigma.mk a) (fun x y h => by cases h; rfl),
        List.idxOf_finRange]
      simp
    · have hm : (⟨a, j⟩ : Σ x, Fin (sizes x)) ∉
          (List.finRange (sizes x)).map (Sigma.mk x) := by
        intro hm
        rcases List.mem_map.mp hm with ⟨k, _, hk⟩
        exact h (congrArg Sigma.fst hk)
      rw [List.idxOf_append_of_notMem hm, List.length_map, List.length_finRange,
        ih (List.mem_of_ne_of_mem (Ne.symm h) ha), List.idxOf_cons_ne xs h]
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

def offset {n : Nat} (padding : Fin n → Nat) (k : Nat) : Nat :=
  (((List.finRange n).take k).map padding).sum

theorem sigma_length {A : Type*} (sizes : A → Nat) (xs : List A) :
    (xs.sigma (fun x => List.finRange (sizes x))).length = (xs.map sizes).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.sigma_cons, ih]

theorem paddingOrder_val {n : Nat} (padding : Fin n → Nat)
    (v : Fin n) (j : Fin (padding v)) :
    (PreprocessingRegularTables.paddingOrder padding ⟨v, j⟩).val =
      offset padding v.val + j.val := by
  change (paddingList padding).idxOf ⟨v, j⟩ = _
  have h := sigma_idxOf padding (List.finRange n) v (List.mem_finRange v) j
  simpa only [List.idxOf_finRange, paddingList, offset] using h

theorem vertexOrder_dummy_val (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) (v : Fin t.vertices) (j : Fin (padding v)) :
    (vertexOrder t padding (Sum.inr ⟨v, j⟩)).val =
      t.darts + offset padding v.val + j.val := by
  rw [vertexOrder_dummy, paddingOrder_val]
  omega

@[simp] theorem offset_zero {n : Nat} (padding : Fin n → Nat) : offset padding 0 = 0 := by
  simp [offset]

theorem offset_all {n : Nat} (padding : Fin n → Nat) :
    offset padding n = ∑ v, padding v := by
  have ht : (List.finRange n).take n = List.finRange n := by simp
  unfold offset
  rw [ht, ← sigma_length padding (List.finRange n)]
  exact paddingList_length padding

end MinUncutGames.Foundations.PCP.PreprocessingPaddingOffsets

end

end OAI
