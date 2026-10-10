import Mathlib

namespace OAI

namespace Problem315.CrossBlock

open scoped BigOperators

abbrev Matrix := Fin 2 → Fin 2 → Bool

def entry (M : Matrix) (i j : Fin 2) : Nat := if M i j then 1 else 0

def row (M : Matrix) (i : Fin 2) : Nat := ∑ j, entry M i j

def col (M : Matrix) (j : Fin 2) : Nat := ∑ i, entry M i j

def total (M : Matrix) : Nat := ∑ i, row M i

def count (s r c : Nat) : Nat :=
  (Finset.univ.filter (fun M : Matrix => total M = s ∧ row M 0 = r ∧ col M 0 = c)).card

theorem count_two : ∀ r c : Fin 3,
    count 2 r c = if r = 1 then (if c = 1 then 2 else 1) else (if c = 1 then 1 else 0) := by
  decide

theorem count_one : ∀ r c : Fin 3,
    count 1 r c = if r ≤ 1 ∧ c ≤ 1 then 1 else 0 := by
  decide

theorem count_three : ∀ r c : Fin 3,
    count 3 r c = if 1 ≤ r ∧ 1 ≤ c then 1 else 0 := by
  decide

theorem count_zero : ∀ r c : Fin 3,
    count 0 r c = if r = 0 ∧ c = 0 then 1 else 0 := by
  decide

theorem count_four : ∀ r c : Fin 3,
    count 4 r c = if r = 2 ∧ c = 2 then 1 else 0 := by
  decide

theorem off_center_disjoint : ∀ M : Matrix,
    total M = 2 → row M 0 ≠ 1 → col M 0 = 1 := by
  decide

theorem central_iff : ∀ M : Matrix,
    total M = 2 →
      (row M 0 = 1 ∧ col M 0 = 1 ↔ (∀ i, row M i = 1) ∧ ∀ j, col M j = 1) := by
  decide

def toggle (M : Matrix) : Matrix :=
  if (∀ i, row M i = 1) ∧ (∀ j, col M j = 1) then
    fun i j => !(M i j)
  else M

theorem toggle_involutive : ∀ M : Matrix, toggle (toggle M) = M := by
  decide

theorem toggle_row : ∀ (M : Matrix) (i : Fin 2), row (toggle M) i = row M i := by
  decide

theorem toggle_col : ∀ (M : Matrix) (j : Fin 2), col (toggle M) j = col M j := by
  decide

theorem toggle_total : ∀ M : Matrix, total (toggle M) = total M := by
  decide

theorem toggle_ne_iff : ∀ M : Matrix,
    toggle M ≠ M ↔ (∀ i, row M i = 1) ∧ ∀ j, col M j = 1 := by
  decide

theorem row_le_two : ∀ (M : Matrix) (i : Fin 2), row M i ≤ 2 := by
  decide

theorem col_le_two : ∀ (M : Matrix) (j : Fin 2), col M j ≤ 2 := by
  decide

theorem total_le_four : ∀ M : Matrix, total M ≤ 4 := by
  decide

theorem count_two_real (r c : Fin 3) :
    (count 2 r c : ℝ) =
      2 - (if r = 1 then 0 else 1) - (if c = 1 then 0 else 1) := by
  rw [count_two]
  by_cases hr : r = 1 <;> by_cases hc : c = 1 <;> norm_num [hr, hc]

end Problem315.CrossBlock

end OAI
