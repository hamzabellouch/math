import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI

/-!
# A counted implementation of the sort used by the streams

The merge follows each comparison branch and counts its steps. The bounded
recursive sort is exactly List.mergeSort once its depth accommodates the
input length. Its ledger includes list-length/split scans and merge work,
giving a linear cost per recursion level, without a quadratic sorting bound.
-/

namespace LowSpaceSubsetSum
namespace CountedSort

variable {α : Type*}

def merge (cmp : α → α → Bool) (xs ys : List α) : List α × ℕ :=
  match xs, ys with
  | [], ys => (ys, 1)
  | xs, [] => (xs, 1)
  | x :: xs, y :: ys =>
    if cmp x y then
      let out := merge cmp xs (y :: ys)
      (x :: out.1, out.2 + 1)
    else
      let out := merge cmp (x :: xs) ys
      (y :: out.1, out.2 + 1)
termination_by xs.length + ys.length

theorem merge_value (cmp : α → α → Bool) (xs ys : List α) :
    (merge cmp xs ys).1 = xs.merge ys cmp := by
  induction xs generalizing ys with
  | nil => simp [merge]
  | cons x xs ih =>
    induction ys with
    | nil => simp [merge]
    | cons y ys ihy =>
      cases h : cmp x y <;> simp [merge, h, ih, ihy]

theorem merge_steps (cmp : α → α → Bool) (xs ys : List α) :
    (merge cmp xs ys).2 ≤ xs.length + ys.length + 1 := by
  induction xs generalizing ys with
  | nil => simp [merge]
  | cons x xs ih =>
    induction ys with
    | nil => simp [merge]
    | cons y ys ihy =>
      cases h : cmp x y
      · simp only [merge, h, Bool.false_eq_true, ↓reduceIte]
        have := ihy
        simp only [List.length_cons] at *
        omega
      · simp only [merge, h, ↓reduceIte]
        have := ih (y :: ys)
        simp only [List.length_cons] at *
        omega

def run (cmp : α → α → Bool) : ℕ → List α → List α × ℕ
  | 0, xs => (xs, 1)
  | _ + 1, [] => ([], 1)
  | _ + 1, [x] => ([x], 1)
  | k + 1, x :: y :: rest =>
    let xs := x :: y :: rest
    let cut := (xs.length + 1) / 2
    let left := run cmp k (xs.take cut)
    let right := run cmp k (xs.drop cut)
    let out := merge cmp left.1 right.1
    (out.1, left.2 + right.2 + 3 * xs.length + out.2 + 1)

theorem run_length (cmp : α → α → Bool) (k : ℕ) (xs : List α) :
    (run cmp k xs).1.length = xs.length := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y rest =>
        simp only [run, merge_value, List.length_merge, ih, List.length_take,
          List.length_drop, List.length_cons]
        omega

theorem run_value (cmp : α → α → Bool) (k : ℕ) (xs : List α) (hk : xs.length ≤ 2 ^ k) :
    (run cmp k xs).1 = xs.mergeSort cmp := by
  induction k generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [run]
    | cons x xs =>
      cases xs with
      | nil => simp [run]
      | cons y rest => simp only [List.length_cons, pow_zero] at hk; omega
  | succ k ih =>
    cases xs with
    | nil => simp [run]
    | cons x xs =>
      cases xs with
      | nil => simp [run]
      | cons y rest =>
        let xs := x :: y :: rest
        let cut := (xs.length + 1) / 2
        have hl : (xs.take cut).length ≤ 2 ^ k := by
          simp only [List.length_cons, pow_succ] at hk
          dsimp only [xs, cut]
          simp only [List.length_take, List.length_cons]
          omega
        have hr : (xs.drop cut).length ≤ 2 ^ k := by
          simp only [List.length_cons, pow_succ] at hk
          dsimp only [xs, cut]
          simp only [List.length_drop, List.length_cons]
          omega
        rw [run, merge_value, ih _ hl, ih _ hr]
        simp only [List.mergeSort, List.MergeSort.Internal.splitInTwo_fst,
          List.MergeSort.Internal.splitInTwo_snd]
        rfl

theorem run_steps (cmp : α → α → Bool) (k : ℕ) (xs : List α) :
    (run cmp k xs).2 ≤ (6 * k + 1) * xs.length + 1 := by
  induction k generalizing xs with
  | zero => simp [run]
  | succ k ih =>
    cases xs with
    | nil => simp [run]
    | cons x xs =>
      cases xs with
      | nil => simp [run]
      | cons y rest =>
        let xs := x :: y :: rest
        let cut := (xs.length + 1) / 2
        have hl := ih (xs.take cut)
        have hr := ih (xs.drop cut)
        have hm := merge_steps cmp (run cmp k (xs.take cut)).1 (run cmp k (xs.drop cut)).1
        rw [run_length, run_length] at hm
        have hparts : (xs.take cut).length + (xs.drop cut).length = xs.length := by
          simp only [List.length_take, List.length_drop]
          omega
        have hn : 2 ≤ xs.length := by simp [xs]
        change (run cmp k (xs.take cut)).2 + (run cmp k (xs.drop cut)).2 +
          3 * xs.length + (merge cmp (run cmp k (xs.take cut)).1
            (run cmp k (xs.drop cut)).1).2 + 1 ≤ (6 * (k + 1) + 1) * xs.length + 1
        nlinarith

def sort (cmp : α → α → Bool) (xs : List α) : List α × ℕ :=
  run cmp (Nat.clog 2 xs.length) xs

theorem sort_value (cmp : α → α → Bool) (xs : List α) :
    (sort cmp xs).1 = xs.mergeSort cmp :=
  run_value cmp _ xs (Nat.le_pow_clog (by decide : 1 < 2) xs.length)

theorem sort_steps (cmp : α → α → Bool) (xs : List α) :
    (sort cmp xs).2 ≤ (6 * Nat.clog 2 xs.length + 1) * xs.length + 1 :=
  run_steps cmp _ xs

theorem sort_steps_of_index_bits (cmp : α → α → Bool) (xs : List α) (n : ℕ)
    (hn : xs.length ≤ 2 ^ n) : (sort cmp xs).2 ≤ (6 * n + 1) * xs.length + 1 := by
  have hdepth : Nat.clog 2 xs.length ≤ n := Nat.clog_le_of_le_pow hn
  exact (sort_steps cmp xs).trans (by gcongr)

end CountedSort
end LowSpaceSubsetSum

end OAI
