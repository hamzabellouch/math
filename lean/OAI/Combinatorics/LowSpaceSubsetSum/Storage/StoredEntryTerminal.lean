import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredEntry
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredSort
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorTerminal

namespace OAI

/-! # Executed terminal weight check on bounded stored entries

The mask list is retained by reference throughout sorting and matching.
Only scalar weights are inspected. The ambient size bounds the sort depth,
so initialization does not compute a logarithm of a list.
-/

namespace LowSpaceSubsetSum.StoredEntryTerminal

variable {n : ℕ}

private def lengthAcc {α : Type*} : List α → ℕ → ℕ → ℕ × ℕ
  | [], count, work => (count, work + 1)
  | _ :: xs, count, work => lengthAcc xs (count + 1) (work + 2)

private theorem lengthAcc_eq {α : Type*} (xs : List α) (count work : ℕ) :
    lengthAcc xs count work = (count + xs.length, work + 2 * xs.length + 1) := by
  induction xs generalizing count work with
  | nil => simp [lengthAcc]
  | cons x xs ih => simp only [lengthAcc, ih, List.length_cons]; congr 1 <;> omega

/-- Tail-recursive matching with each scalar subtraction and comparison charged. -/
def findAcc (target : ℤ) : ℕ → List (StoredEntry n) → List (StoredEntry n) → ℕ → Bool × ℕ
  | 0, _, _, work => (false, work + 1)
  | _ + 1, [], _, work => (false, work + 2)
  | _ + 1, _ :: _, [], work => (false, work + 3)
  | fuel + 1, x :: xs, y :: ys, work =>
    let a := x.value
    let b := target - y.value
    if a < b then findAcc target fuel xs (y :: ys) (work + 8)
    else if b < a then findAcc target fuel (x :: xs) ys (work + 9)
    else (true, work + 9)

theorem findAcc_value (target : ℤ) (fuel : ℕ) (xs ys : List (StoredEntry n))
    (work queries : ℕ) :
    (findAcc target fuel xs ys work).1 =
      (SortedFind.runAcc SeparatorTerminal.read StoredEntry.value SeparatorTerminal.read
        (fun y : StoredEntry n => target - y.value) fuel xs ys queries).1 := by
  induction fuel generalizing xs ys work queries with
  | zero => rfl
  | succ fuel ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases ys with
      | nil => rfl
      | cons y ys =>
        simp only [findAcc, SortedFind.runAcc, SeparatorTerminal.read]
        split
        · exact ih _ _ _ _
        · split
          · exact ih _ _ _ _
          · rfl

theorem findAcc_work (target : ℤ) (fuel : ℕ) (xs ys : List (StoredEntry n))
    (work : ℕ) : (findAcc target fuel xs ys work).2 ≤ work + 10 * (fuel + 1) := by
  induction fuel generalizing xs ys work with
  | zero => simp [findAcc]
  | succ fuel ih =>
    cases xs with
    | nil => simp only [findAcc]; omega
    | cons x xs =>
      cases ys with
      | nil => simp only [findAcc]; omega
      | cons y ys =>
        simp only [findAcc]
        split
        · exact (ih _ _ _).trans (by omega)
        · split
          · exact (ih _ _ _).trans (by omega)
          · dsimp; omega

def leftCompare (x y : StoredEntry n) : Bool × ℕ := (decide (x.value ≤ y.value), 3)

def rightCompare (target : ℤ) (x y : StoredEntry n) : Bool × ℕ :=
  (decide (target - x.value ≤ target - y.value), 5)

/-- The two lengths are computed once and reused as the matching limit. -/
def run (target : ℤ) (xs ys : List (StoredEntry n)) : Bool × ℕ :=
  let nx := lengthAcc xs 0 0
  let ny := lengthAcc ys 0 0
  if xs.isEmpty || ys.isEmpty then (false, nx.2 + ny.2 + 3) else
    let left := MeasuredSort.run leftCompare n xs
    let right := MeasuredSort.run (rightCompare target) n ys
    let out := findAcc target (nx.1 + ny.1 + 1) left.1 right.1 0
    (out.1, nx.2 + ny.2 + left.2 + right.2 + out.2 + 5)

private theorem left_value (xs : List (StoredEntry n)) (hx : xs.length ≤ 2 ^ n) :
    (MeasuredSort.run leftCompare n xs).1 = (SeparatorTerminal.sort StoredEntry.value xs).1 := by
  rw [MeasuredSort.run_value, CountedSort.run_value _ _ _ hx,
    SeparatorTerminal.sort, CountedSort.sort_value]
  rfl

private theorem right_value (target : ℤ) (ys : List (StoredEntry n))
    (hy : ys.length ≤ 2 ^ n) :
    (MeasuredSort.run (rightCompare target) n ys).1 =
      (SeparatorTerminal.sort (fun y : StoredEntry n => target - y.value) ys).1 := by
  rw [MeasuredSort.run_value, CountedSort.run_value _ _ _ hy,
    SeparatorTerminal.sort, CountedSort.sort_value]
  rfl

theorem run_value (target : ℤ) (xs ys : List (StoredEntry n))
    (hx : xs.length ≤ 2 ^ n) (hy : ys.length ≤ 2 ^ n) :
    (run target xs ys).1 =
      (SeparatorTerminal.run StoredEntry.value StoredEntry.value target xs ys).accepted := by
  simp only [run, SeparatorTerminal.run, lengthAcc_eq, Nat.zero_add]
  split
  · rfl
  · rw [findAcc_value target _ _ _ 0 0, left_value xs hx, right_value target ys hy]

theorem run_work (target : ℤ) (xs ys : List (StoredEntry n)) :
    (run target xs ys).2 ≤ 64 * (n + 1) * (xs.length + ys.length + 1) := by
  have hl := MeasuredSort.run_work (leftCompare (n := n)) 3 (by intros; exact le_rfl) n xs
  have hr := MeasuredSort.run_work (rightCompare (n := n) target) 5 (by intros; exact le_rfl) n ys
  have hsl := CountedSort.run_steps (fun x y : StoredEntry n => (leftCompare x y).1) n xs
  have hsr := CountedSort.run_steps
    (fun x y : StoredEntry n => (rightCompare target x y).1) n ys
  have hl' := hl.trans (Nat.mul_le_mul_left _ hsl)
  have hr' := hr.trans (Nat.mul_le_mul_left _ hsr)
  have hf := findAcc_work target (xs.length + ys.length + 1)
    (MeasuredSort.run leftCompare n xs).1 (MeasuredSort.run (rightCompare target) n ys).1 0
  simp only [run, lengthAcc_eq, Nat.zero_add]
  split
  · dsimp; nlinarith only [Nat.zero_le n, Nat.zero_le xs.length, Nat.zero_le ys.length]
  · dsimp only
    nlinarith only [hl', hr', hf, Nat.zero_le n, Nat.zero_le xs.length, Nat.zero_le ys.length,
      Nat.zero_le (n * xs.length), Nat.zero_le (n * ys.length)]

/-- This bounded terminal agrees with the separator depth-first search. -/
theorem bounded_value (target : ℤ) (xs ys : List (StoredEntry n))
    (h : xs.length + ys.length ≤ 2 ^ n) :
    (run target xs ys).1 =
      (SeparatorTerminal.bounded n StoredEntry.value StoredEntry.value target xs ys).accepted := by
  simp only [SeparatorTerminal.bounded, h, ↓reduceIte]
  exact run_value target xs ys (by omega) (by omega)

theorem correct (target : ℤ) (xs ys : List (StoredEntry n))
    (hx : xs.length ≤ 2 ^ n) (hy : ys.length ≤ 2 ^ n) :
    (run target xs ys).1 = true ↔
      ∃ x ∈ xs, ∃ y ∈ ys, x.value + y.value = target := by
  rw [run_value target xs ys hx hy]
  exact SeparatorTerminal.correct _ _ _ _ _

/-- Erasure to the original finite-set record is only a proof view. -/
theorem semantic_value (target : ℤ) (xs ys : List (StoredEntry n))
    (hx : xs.length ≤ 2 ^ n) (hy : ys.length ≤ 2 ^ n) :
    (run target xs ys).1 =
      (SeparatorTerminal.run Entry.value Entry.value target
        (xs.map StoredEntry.semantic) (ys.map StoredEntry.semantic)).accepted := by
  apply Bool.eq_iff_iff.mpr
  rw [correct target xs ys hx hy, SeparatorTerminal.correct]
  simp only [List.mem_map, exists_exists_and_eq_and, StoredEntry.semantic]

/-- The matching limit is the sum of the two counted lengths. -/
theorem run_expanded (target : ℤ) (xs ys : List (StoredEntry n)) :
    run target xs ys =
      if xs.isEmpty || ys.isEmpty then
        (false, (2 * xs.length + 1) + (2 * ys.length + 1) + 3)
      else
        let left := MeasuredSort.run leftCompare n xs
        let right := MeasuredSort.run (rightCompare target) n ys
        let out := findAcc target (xs.length + ys.length + 1) left.1 right.1 0
        (out.1, (2 * xs.length + 1) + (2 * ys.length + 1) + left.2 + right.2 + out.2 + 5) := by
  simp only [run, lengthAcc_eq, Nat.zero_add]

end LowSpaceSubsetSum.StoredEntryTerminal

end OAI
