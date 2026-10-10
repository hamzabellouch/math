import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredSort

namespace OAI

/-! # Live list and continuation cells of the executed mergesort

The first projection is exactly the measured sort, including its work
counter. The second projection records list and continuation storage;
comparison callbacks are scalar operations at the terminal application.
Input record payloads are shared and are not copied by a list cons.
-/

namespace LowSpaceSubsetSum.MeasuredSortSpace

variable {α : Type*}

/-- The merge retains its input tails, one continuation per selected head,
and the newly constructed result spine. -/
def merge (cmp : α → α → Bool × ℕ) (xs ys : List α) : (List α × ℕ) × ℕ :=
  match xs, ys with
  | [], ys => ((ys, 1), ys.length + 2)
  | xs, [] => ((xs, 1), xs.length + 2)
  | x :: xs, y :: ys =>
    let c := cmp x y
    if c.1 then
      let out := merge cmp xs (y :: ys)
      ((x :: out.1.1, out.1.2 + c.2 + 1),
        max ((x :: xs).length + (y :: ys).length + 2) (out.2 + 4))
    else
      let out := merge cmp (x :: xs) ys
      ((y :: out.1.1, out.1.2 + c.2 + 1),
        max ((x :: xs).length + (y :: ys).length + 2) (out.2 + 4))
termination_by xs.length + ys.length

theorem merge_value (cmp : α → α → Bool × ℕ) (xs ys : List α) :
    (merge cmp xs ys).1 = MeasuredSort.merge cmp xs ys := by
  induction xs generalizing ys with
  | nil => simp [merge, MeasuredSort.merge]
  | cons x xs ih =>
    induction ys with
    | nil => simp [merge, MeasuredSort.merge]
    | cons y ys ihy =>
      cases h : (cmp x y).1 <;> simp [merge, MeasuredSort.merge, h, ih, ihy]

theorem merge_cells (cmp : α → α → Bool × ℕ) (xs ys : List α) :
    (merge cmp xs ys).2 ≤ 6 * (xs.length + ys.length + 1) := by
  induction xs generalizing ys with
  | nil => simp only [merge, List.length_nil]; omega
  | cons x xs ih =>
    induction ys with
    | nil => simp only [merge, List.length_nil]; omega
    | cons y ys ihy =>
      have hx := ih (y :: ys)
      cases h : (cmp x y).1 <;>
        simp only [merge, h, Bool.false_eq_true, ↓reduceIte, List.length_cons, max_le_iff] <;>
        simp only [List.length_cons] at hx ihy <;> constructor <;> omega

/-- One branch runs at a time. The parent input, split spines and completed
sibling fit in the eight-cell-per-input local allowance. -/
def run (cmp : α → α → Bool × ℕ) : ℕ → List α → (List α × ℕ) × ℕ
  | 0, xs => ((xs, 1), xs.length + 2)
  | _ + 1, [] => (([], 1), 2)
  | _ + 1, [x] => (([x], 1), 3)
  | k + 1, x :: y :: rest =>
    let xs := x :: y :: rest
    let cut := (xs.length + 1) / 2
    let left := run cmp k (xs.take cut)
    let right := run cmp k (xs.drop cut)
    let out := merge cmp left.1.1 right.1.1
    ((out.1.1, left.1.2 + right.1.2 + 3 * xs.length + out.1.2 + 1),
      8 * (xs.length + 1) + max left.2 (max right.2 out.2))

theorem run_value (cmp : α → α → Bool × ℕ) (k : ℕ) (xs : List α) :
    (run cmp k xs).1 = MeasuredSort.run cmp k xs := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y rest => simp only [run, merge_value, ih, MeasuredSort.run]

theorem run_length (cmp : α → α → Bool × ℕ) (k : ℕ) (xs : List α) :
    (run cmp k xs).1.1.length = xs.length := by
  rw [run_value, MeasuredSort.run_value]
  exact CountedSort.run_length _ _ _

theorem run_cells (cmp : α → α → Bool × ℕ) (k : ℕ) (xs : List α) :
    (run cmp k xs).2 ≤ 32 * (k + 1) * (xs.length + 1) := by
  induction k generalizing xs with
  | zero => simp only [run]; omega
  | succ k ih =>
    cases xs with
    | nil => simp only [run, List.length_nil]; omega
    | cons x tail =>
      cases tail with
      | nil => simp only [run, List.length_cons, List.length_nil]; omega
      | cons y rest =>
        let xs := x :: y :: rest
        let cut := (xs.length + 1) / 2
        have hl := ih (xs.take cut)
        have hr := ih (xs.drop cut)
        have hll : (xs.take cut).length ≤ xs.length := by
          simp only [List.length_take]
          exact Nat.min_le_right _ _
        have hrl : (xs.drop cut).length ≤ xs.length := by simp only [List.length_drop]; omega
        have hleft := hl.trans (Nat.mul_le_mul_left (32 * (k + 1)) (by omega :
          (xs.take cut).length + 1 ≤ xs.length + 1))
        have hright := hr.trans (Nat.mul_le_mul_left (32 * (k + 1)) (by omega :
          (xs.drop cut).length + 1 ≤ xs.length + 1))
        have hm := merge_cells cmp (run cmp k (xs.take cut)).1.1
          (run cmp k (xs.drop cut)).1.1
        rw [run_length, run_length, List.length_take, List.length_drop] at hm
        have hm' : (merge cmp (run cmp k (xs.take cut)).1.1
            (run cmp k (xs.drop cut)).1.1).2 ≤ 6 * (xs.length + 1) := by
          convert hm using 1
          omega
        have hm'' := hm'.trans (Nat.mul_le_mul_right (xs.length + 1)
          (show 6 ≤ 32 * (k + 1) by omega))
        have hmax := max_le hleft (max_le hright hm'')
        change 8 * (xs.length + 1) + _ ≤ 32 * (k + 1 + 1) * (xs.length + 1)
        nlinarith only [hmax, Nat.zero_le xs.length]

end LowSpaceSubsetSum.MeasuredSortSpace

end OAI
