import OAI.Combinatorics.LowSpaceSubsetSum.Storage.LeafEnumeration

namespace OAI

/-! # Output-sensitive fixed-cardinality subset generation

Infeasible recursive branches are pruned before they recurse. The work
counter charges the feasibility scan, recursive calls, append and map; this
avoids charging all subsets of a block when only one cardinality is needed.
-/

namespace LowSpaceSubsetSum.CountedSubsets

variable {α : Type*}

def all : List α → List (List α) × ℕ
  | [] => ([[]], 1)
  | x :: xs =>
    let rest := all xs
    (rest.1.flatMap (fun S => [S, x :: S]), rest.2 + 3 * rest.1.length + 1)

theorem all_value (xs : List α) : (all xs).1 = xs.sublists := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [all, ih, List.sublists_cons, List.bind_eq_flatMap]

theorem all_length (xs : List α) : (all xs).1.length = 2 ^ xs.length := by
  rw [all_value, List.length_sublists]

theorem all_work (xs : List α) : (all xs).2 ≤ 4 * 2 ^ xs.length := by
  induction xs with
  | nil => norm_num [all]
  | cons x xs ih =>
    simp only [all, all_length, List.length_cons, pow_succ]
    have hp : 1 ≤ 2 ^ xs.length := Nat.one_le_two_pow
    omega

def select (k : ℕ) (xs : List α) : List (List α) × ℕ :=
  match k, xs with
  | 0, _ => ([[]], 1)
  | _ + 1, [] => ([], 1)
  | k + 1, x :: xs =>
    if k + 1 ≤ xs.length + 1 then
      let left := select (k + 1) xs
      let right := select k xs
      (left.1 ++ right.1.map (List.cons x),
        left.2 + right.2 + left.1.length + right.1.length + xs.length + 2)
    else ([], xs.length + 2)
termination_by xs.length

theorem select_value (k : ℕ) (xs : List α) : (select k xs).1 = xs.sublistsLen k := by
  induction xs generalizing k with
  | nil => cases k <;> simp [select]
  | cons x xs ih =>
    cases k with
    | zero => simp [select]
    | succ k =>
      rw [select]
      split
      · simp only [ih, List.sublistsLen_succ_cons]
      · rename_i h
        symm
        apply List.eq_nil_of_length_eq_zero
        rw [List.length_sublistsLen]
        exact Nat.choose_eq_zero_of_lt (by simp only [List.length_cons]; omega)

theorem select_length (k : ℕ) (xs : List α) :
    (select k xs).1.length = xs.length.choose k := by
  rw [select_value, List.length_sublistsLen]

theorem select_infeasible (k : ℕ) (xs : List α) (hk : xs.length < k) :
    (select k xs).2 ≤ xs.length + 1 := by
  cases k with
  | zero => omega
  | succ k =>
    cases xs with
    | nil => simp [select]
    | cons x xs => simp only [List.length_cons] at hk ⊢; simp [select, show ¬ k + 1 ≤ xs.length + 1 by omega]

/-- The count is quadratic in the domain length and linear in the exact
number of selected subsets, including the boundary cases `k=0` and `k=n`. -/
theorem select_work (k : ℕ) (xs : List α) (hk : k ≤ xs.length) :
    (select k xs).2 ≤ 4 * (xs.length + 1) ^ 2 * xs.length.choose k := by
  induction xs generalizing k with
  | nil =>
    have he : k = 0 := by simpa using hk
    subst k
    simp [select]
  | cons x xs ih =>
    cases k with
    | zero =>
      simp only [select, List.length_cons, Nat.choose_zero_right, mul_one]
      have hp : 1 ≤ (xs.length + 1 + 1) ^ 2 := one_le_pow₀ (by omega)
      omega
    | succ k =>
      have hk' : k ≤ xs.length := by simp only [List.length_cons] at hk; omega
      have hr := ih k hk'
      have hpos : 1 ≤ xs.length.choose k := Nat.choose_pos hk'
      have hfeas : k + 1 ≤ xs.length + 1 := by simpa only [List.length_cons] using hk
      simp only [select, ite_eq_left hfeas, select_length, List.length_cons]
      by_cases hleft : k + 1 ≤ xs.length
      · have hl := ih (k + 1) hleft
        have hsum : xs.length.choose (k + 1) + xs.length.choose k =
            (xs.length + 1).choose (k + 1) := by
          simpa only [Nat.succ_eq_add_one, Nat.add_comm] using
            (Nat.choose_succ_succ xs.length k).symm
        rw [← hsum]
        nlinarith only [hl, hr, hpos]
      · have he : k = xs.length := by omega
        subst k
        have hl := select_infeasible (xs.length + 1) xs (by omega)
        simp only [Nat.choose_self, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self _)] at hr ⊢
        nlinarith only [hl, hr]

end LowSpaceSubsetSum.CountedSubsets

end OAI
