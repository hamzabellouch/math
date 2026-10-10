import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredSort

namespace OAI

/-! # Live cells of measured mergesort

Recursive merge retains a bounded frame per emitted item. Mergesort retains
its split lists and the completed left result during the right recursion.
The trace counts list nodes and bounded record payloads explicitly.
-/

namespace LowSpaceSubsetSum.MeasuredSortCells

variable {α : Type*}

def merge (X : ℕ) (cmp : α → (α → (Bool × ℕ) × ℕ)) (xs ys : List α) :
    (List α × ℕ) × ℕ :=
  match xs, ys with
  | [], ys => ((ys, 1), (X + 1) * (ys.length + 1) + 8)
  | xs, [] => ((xs, 1), (X + 1) * (xs.length + 1) + 8)
  | x :: xs, y :: ys =>
    let c := cmp x y
    if c.1.1 then
      let out := merge X cmp xs (y :: ys)
      ((x :: out.1.1, out.1.2 + c.1.2 + 1), max (c.2 + 4 * X + 20) (out.2 + 4 * X + 20))
    else
      let out := merge X cmp (x :: xs) ys
      ((y :: out.1.1, out.1.2 + c.1.2 + 1), max (c.2 + 4 * X + 20) (out.2 + 4 * X + 20))
termination_by xs.length + ys.length

theorem merge_value (X : ℕ) (cmp : α → α → (Bool × ℕ) × ℕ) (xs ys : List α) :
    (merge X cmp xs ys).1 = MeasuredSort.merge (fun x y => (cmp x y).1) xs ys := by
  induction xs generalizing ys with
  | nil => simp only [merge, MeasuredSort.merge]
  | cons x xs ih =>
    induction ys with
    | nil => simp only [merge, MeasuredSort.merge]
    | cons y ys ihy =>
      rw [merge, MeasuredSort.merge]
      split <;> simp only [ih, ihy]

theorem merge_cells (X : ℕ) (cmp : α → α → (Bool × ℕ) × ℕ) (R : ℕ)
    (hc : ∀ x y, (cmp x y).2 ≤ R) (xs ys : List α) :
    (merge X cmp xs ys).2 ≤ (4 * X + 20) * (xs.length + ys.length + 1) + R := by
  induction xs generalizing ys with
  | nil => simp only [merge, List.length_nil, Nat.zero_add]; nlinarith only [Nat.zero_le (X * ys.length)]
  | cons x xs ih =>
    induction ys with
    | nil => simp only [merge, List.length_nil, Nat.add_zero]; nlinarith only [Nat.zero_le (X * xs.length)]
    | cons y ys ihy =>
      have hcost := hc x y
      have hleft := ih (y :: ys)
      rw [merge]
      split
      · dsimp only
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hleft ⊢
        omega
      · dsimp only
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at ihy ⊢
        omega

def run (X : ℕ) (cmp : α → α → (Bool × ℕ) × ℕ) : ℕ → List α → (List α × ℕ) × ℕ
  | 0, xs => ((xs, 1), (X + 1) * (xs.length + 1) + 8)
  | _ + 1, [] => (([], 1), X + 16)
  | _ + 1, [x] => (([x], 1), 2 * X + 16)
  | k + 1, x :: y :: rest =>
    let xs := x :: y :: rest
    let cut := (xs.length + 1) / 2
    let left := run X cmp k (xs.take cut)
    let right := run X cmp k (xs.drop cut)
    let out := merge X cmp left.1.1 right.1.1
    let kept := 4 * (X + 1) * (xs.length + 1) + 32
    ((out.1.1, left.1.2 + right.1.2 + 3 * xs.length + out.1.2 + 1),
      max (kept + left.2) (max (kept + right.2) (kept + out.2)))

theorem run_value (X : ℕ) (cmp : α → α → (Bool × ℕ) × ℕ) (k : ℕ) (xs : List α) :
    (run X cmp k xs).1 = MeasuredSort.run (fun x y => (cmp x y).1) k xs := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y rest => simp only [run, MeasuredSort.run, merge_value, ih]

theorem run_length (X : ℕ) (cmp : α → α → (Bool × ℕ) × ℕ) (k : ℕ) (xs : List α) :
    (run X cmp k xs).1.1.length = xs.length := by
  rw [run_value, MeasuredSort.run_value, CountedSort.run_length]

theorem run_cells (X : ℕ) (cmp : α → α → (Bool × ℕ) × ℕ) (R : ℕ)
    (hc : ∀ x y, (cmp x y).2 ≤ R) (k : ℕ) (xs : List α) :
    (run X cmp k xs).2 ≤ (k + 1) * (24 * (X + 2) * (xs.length + 1) + R) := by
  induction k generalizing xs with
  | zero => simp only [run, Nat.zero_add, Nat.one_mul]; nlinarith only [Nat.zero_le (X * xs.length)]
  | succ k ih =>
    cases xs with
    | nil => simp only [run, List.length_nil, Nat.zero_add, Nat.mul_one]; nlinarith
    | cons x xs =>
      cases xs with
      | nil => simp only [run, List.length_cons, List.length_nil]; nlinarith
      | cons y rest =>
        let xs := x :: y :: rest
        let cut := (xs.length + 1) / 2
        have hl := ih (xs.take cut)
        have hr := ih (xs.drop cut)
        have hll : (xs.take cut).length ≤ xs.length := by
          simp only [List.length_take]
          exact Nat.min_le_right _ _
        have hrr : (xs.drop cut).length ≤ xs.length := by
          simp only [List.length_drop]
          omega
        have hcL := Nat.mul_le_mul_left (k + 1) (Nat.add_le_add_right
          (Nat.mul_le_mul_left (24 * (X + 2)) (Nat.add_le_add_right hll 1)) R)
        have hcR := Nat.mul_le_mul_left (k + 1) (Nat.add_le_add_right
          (Nat.mul_le_mul_left (24 * (X + 2)) (Nat.add_le_add_right hrr 1)) R)
        have hm := merge_cells X cmp R hc (run X cmp k (xs.take cut)).1.1
          (run X cmp k (xs.drop cut)).1.1
        rw [run_length, run_length] at hm
        have hparts : (xs.take cut).length + (xs.drop cut).length = xs.length := by
          simp only [List.length_take, List.length_drop]; omega
        rw [hparts] at hm
        change max (4 * (X + 1) * (xs.length + 1) + 32 + (run X cmp k (xs.take cut)).2)
          (max (4 * (X + 1) * (xs.length + 1) + 32 + (run X cmp k (xs.drop cut)).2)
            (4 * (X + 1) * (xs.length + 1) + 32 + (merge X cmp (run X cmp k (xs.take cut)).1.1 (run X cmp k (xs.drop cut)).1.1).2)) ≤
            (k + 2) * (24 * (X + 2) * (xs.length + 1) + R)
        have hL := hl.trans hcL
        have hR := hr.trans hcR
        have hkept : 4 * (X + 1) * (xs.length + 1) + 32 ≤ 24 * (X + 2) * (xs.length + 1) + R := by
          nlinarith only [Nat.zero_le (X * xs.length)]
        have hmerge : 4 * (X + 1) * (xs.length + 1) + 32 + (merge X cmp (run X cmp k (xs.take cut)).1.1 (run X cmp k (xs.drop cut)).1.1).2 ≤
            2 * (24 * (X + 2) * (xs.length + 1) + R) := by
          nlinarith only [hm, Nat.zero_le (X * xs.length)]
        simp only [Nat.add_mul, Nat.one_mul] at hL hR ⊢
        omega

end LowSpaceSubsetSum.MeasuredSortCells

end OAI
