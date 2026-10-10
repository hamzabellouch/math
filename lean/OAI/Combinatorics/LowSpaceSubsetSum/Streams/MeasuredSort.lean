import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedSort

namespace OAI

/-! # Mergesort including every comparator callback

The value agrees exactly with the counted merge and sort. The work theorem
scales its structural ledger by a bound on the supplied comparison work.
-/

namespace LowSpaceSubsetSum.MeasuredSort

variable {α : Type*}

def merge (cmp : α → α → Bool × ℕ) (xs ys : List α) : List α × ℕ :=
  match xs, ys with
  | [], ys => (ys, 1)
  | xs, [] => (xs, 1)
  | x :: xs, y :: ys =>
    let c := cmp x y
    if c.1 then
      let out := merge cmp xs (y :: ys)
      (x :: out.1, out.2 + c.2 + 1)
    else
      let out := merge cmp (x :: xs) ys
      (y :: out.1, out.2 + c.2 + 1)
termination_by xs.length + ys.length

theorem merge_value (cmp : α → α → Bool × ℕ) (xs ys : List α) :
    (merge cmp xs ys).1 = (CountedSort.merge (fun x y => (cmp x y).1) xs ys).1 := by
  induction xs generalizing ys with
  | nil => simp [merge, CountedSort.merge]
  | cons x xs ih =>
    induction ys with
    | nil => simp [merge, CountedSort.merge]
    | cons y ys ihy =>
      cases h : (cmp x y).1 <;> simp [merge, CountedSort.merge, h, ih, ihy]

theorem merge_work (cmp : α → α → Bool × ℕ) (K : ℕ)
    (hc : ∀ x y, (cmp x y).2 ≤ K) (xs ys : List α) :
    (merge cmp xs ys).2 ≤
      (K + 1) * (CountedSort.merge (fun x y => (cmp x y).1) xs ys).2 := by
  induction xs generalizing ys with
  | nil => simp [merge, CountedSort.merge]
  | cons x xs ih =>
    induction ys with
    | nil => simp [merge, CountedSort.merge]
    | cons y ys ihy =>
      have hcost := hc x y
      cases h : (cmp x y).1
      · simp only [merge, CountedSort.merge, h, Bool.false_eq_true, ↓reduceIte]
        simp only [Nat.mul_add, Nat.mul_one]
        omega
      · have hi := ih (y :: ys)
        simp only [merge, CountedSort.merge, h, ↓reduceIte]
        simp only [Nat.mul_add, Nat.mul_one]
        omega

def run (cmp : α → α → Bool × ℕ) : ℕ → List α → List α × ℕ
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

theorem run_value (cmp : α → α → Bool × ℕ) (k : ℕ) (xs : List α) :
    (run cmp k xs).1 = (CountedSort.run (fun x y => (cmp x y).1) k xs).1 := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y rest => simp only [run, merge_value, ih, CountedSort.run]

theorem run_work (cmp : α → α → Bool × ℕ) (K : ℕ)
    (hc : ∀ x y, (cmp x y).2 ≤ K) (k : ℕ) (xs : List α) :
    (run cmp k xs).2 ≤ (K + 1) * (CountedSort.run (fun x y => (cmp x y).1) k xs).2 := by
  induction k generalizing xs with
  | zero => simp only [run, CountedSort.run]; omega
  | succ k ih =>
    cases xs with
    | nil => simp only [run, CountedSort.run]; omega
    | cons x xs =>
      cases xs with
      | nil => simp only [run, CountedSort.run]; omega
      | cons y rest =>
        let xs := x :: y :: rest
        let cut := (xs.length + 1) / 2
        have hl := ih (xs.take cut)
        have hr := ih (xs.drop cut)
        have hm := merge_work cmp K hc (run cmp k (xs.take cut)).1 (run cmp k (xs.drop cut)).1
        rw [run_value, run_value] at hm
        change (run cmp k (xs.take cut)).2 + (run cmp k (xs.drop cut)).2 +
          3 * xs.length + (merge cmp (run cmp k (xs.take cut)).1
            (run cmp k (xs.drop cut)).1).2 + 1 ≤
          (K + 1) * ((CountedSort.run (fun x y => (cmp x y).1) k (xs.take cut)).2 +
            (CountedSort.run (fun x y => (cmp x y).1) k (xs.drop cut)).2 + 3 * xs.length +
            (CountedSort.merge (fun x y => (cmp x y).1)
              (CountedSort.run (fun x y => (cmp x y).1) k (xs.take cut)).1
              (CountedSort.run (fun x y => (cmp x y).1) k (xs.drop cut)).1).2 + 1)
        rw [run_value, run_value]
        nlinarith only [hl, hr, hm, Nat.zero_le (K * (3 * xs.length + 1))]

def sort (cmp : α → α → Bool × ℕ) (xs : List α) : List α × ℕ :=
  run cmp (Nat.clog 2 xs.length) xs

theorem sort_value (cmp : α → α → Bool × ℕ) (xs : List α) :
    (sort cmp xs).1 = xs.mergeSort (fun x y => (cmp x y).1) := by
  rw [sort, run_value, CountedSort.run_value]
  exact Nat.le_pow_clog (by decide) _

theorem sort_work (cmp : α → α → Bool × ℕ) (K : ℕ)
    (hc : ∀ x y, (cmp x y).2 ≤ K) (xs : List α) (n : ℕ) (hn : xs.length ≤ 2 ^ n) :
    (sort cmp xs).2 ≤ (K + 1) * ((6 * n + 1) * xs.length + 1) := by
  exact (run_work cmp K hc _ _).trans
    (Nat.mul_le_mul_left _ (CountedSort.sort_steps_of_index_bits _ xs n hn))

end LowSpaceSubsetSum.MeasuredSort

end OAI
