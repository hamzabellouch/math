import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedSort
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionDictionary
import Mathlib.Data.List.Destutter

namespace OAI

/-! # Linear duplicate removal after sorting compressed weights

The output is exactly the compact list used by the decision core.
The implementation removes adjacent repeats and never searches the tail for
a duplicate. Its counter charges one equality test and constant list work
per input occurrence.
-/

namespace LowSpaceSubsetSum.CountedDedup

variable {α : Type*} [DecidableEq α]

def tail (previous : α) : List α → List α × ℕ
  | [] => ([previous], 1)
  | x :: xs =>
    if previous = x then
      let rest := tail previous xs
      (rest.1, rest.2 + 1)
    else
      let rest := tail x xs
      (previous :: rest.1, rest.2 + 1)

def run : List α → List α × ℕ
  | [] => ([], 1)
  | x :: xs => tail x xs

theorem tail_value (previous : α) (xs : List α) :
    (tail previous xs).1 = xs.destutter' (· ≠ ·) previous := by
  induction xs generalizing previous with
  | nil => rfl
  | cons x xs ih =>
    by_cases he : previous = x <;> simp [tail, he, ih]

theorem tail_work (previous : α) (xs : List α) :
    (tail previous xs).2 = xs.length + 1 := by
  induction xs generalizing previous with
  | nil => rfl
  | cons x xs ih => by_cases he : previous = x <;> simp [tail, he, ih]

theorem run_value (xs : List α) : (run xs).1 = xs.destutter (· ≠ ·) := by
  cases xs with
  | nil => rfl
  | cons x xs => simpa only [run, List.destutter_cons'] using tail_value x xs

theorem run_sorted_value (xs : List α) {r : α → α → Prop} [Std.Antisymm r]
    (hs : xs.Pairwise r) : (run xs).1 = xs.dedup := by
  rw [run_value, hs.destutter_eq_dedup]

theorem run_work (xs : List α) : (run xs).2 ≤ xs.length + 1 := by
  cases xs with
  | nil => rfl
  | cons x xs => simp only [run, tail_work, List.length_cons]; omega

end CountedDedup

namespace CompactWeightWork

variable {n : ℕ}

def run (a : Fin n → ℤ) (V : Finset (Fin n)) : List ℤ × ℕ :=
  let sorted := CountedSort.sort (fun x y : ℤ => decide (x ≤ y)) (rawWeightList a V)
  let compact := CountedDedup.run sorted.1
  (compact.1, sorted.2 + compact.2)

theorem run_value (a : Fin n → ℤ) (V : Finset (Fin n)) :
    (run a V).1 = compactWeightList a V := by
  have hs : ((rawWeightList a V).mergeSort (fun x y => decide (x ≤ y))).Pairwise (· ≤ ·) := by
    simpa only [decide_eq_true_eq] using
      (List.pairwise_mergeSort (le := fun x y : ℤ => decide (x ≤ y))
        (fun x y z hxy hyz => decide_eq_true (le_trans (of_decide_eq_true hxy) (of_decide_eq_true hyz)))
        (fun x y => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total x y)
        (rawWeightList a V))
  simp only [run, CountedSort.sort_value, CountedDedup.run_sorted_value _ hs, compactWeightList]

theorem run_work (a : Fin n → ℤ) (V : Finset (Fin n)) :
    (run a V).2 ≤ (6 * n + 2) * 2 ^ V.card + 2 := by
  have hc : V.card ≤ n := (Finset.card_le_univ V).trans_eq (Fintype.card_fin n)
  have hlen : (rawWeightList a V).length ≤ 2 ^ n := by
    rw [rawWeightList_length]
    exact Nat.pow_le_pow_right (by decide) hc
  have hs := CountedSort.sort_steps_of_index_bits (fun x y : ℤ => decide (x ≤ y))
    (rawWeightList a V) n hlen
  have hd := CountedDedup.run_work
    (CountedSort.sort (fun x y : ℤ => decide (x ≤ y)) (rawWeightList a V)).1
  rw [CountedSort.sort_value, List.length_mergeSort, rawWeightList_length] at hd
  rw [rawWeightList_length] at hs
  change (CountedSort.sort (fun x y : ℤ => decide (x ≤ y)) (rawWeightList a V)).2 +
    (CountedDedup.run (CountedSort.sort (fun x y : ℤ => decide (x ≤ y)) (rawWeightList a V)).1).2 ≤ _
  rw [CountedSort.sort_value]
  nlinarith only [hs, hd]

end CompactWeightWork
end LowSpaceSubsetSum

end OAI
