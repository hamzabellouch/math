import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

/-!
# Prefix preservation in an append-only list sequence

Each step appends a finite list to the preceding state. The accumulated
length is a finite sum, and all earlier entries retain their original indices.
-/

namespace ReflexiveFixedPoints.ListRunPrefix

open scoped BigOperators

variable {R : Type*}

/-- Starting from the empty list, the length is the sum of all appended lengths. -/
theorem length_eq_sum (state extra : ℕ → List R)
    (hzero : state 0 = [])
    (hstep : ∀ n, state (n + 1) = state n ++ extra n) (n : ℕ) :
    (state n).length = ∑ i ∈ Finset.range n, (extra i).length := by
  induction n with
  | zero => simp only [hzero, List.length_nil, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
      rw [hstep n, List.length_append, Finset.sum_range_succ, ih]

/-- Every earlier state is an actual initial segment of every later state. -/
theorem prefix_of_le (state extra : ℕ → List R)
    (hstep : ∀ n, state (n + 1) = state n ++ extra n)
    {i j : ℕ} (h : i ≤ j) :
    state i <+: state j := by
  induction h using Nat.leRec with
  | refl => exact List.prefix_rfl
  | @le_succ_of_le j h ih =>
      rw [hstep j]
      exact ih.trans (List.prefix_append (state j) (extra j))

/-- Lengths cannot decrease along the append sequence. -/
theorem length_le_of_le (state extra : ℕ → List R)
    (hstep : ∀ n, state (n + 1) = state n ++ extra n)
    {i j : ℕ} (h : i ≤ j) :
    (state i).length ≤ (state j).length :=
  (prefix_of_le state extra hstep h).length_le

/-- Taking the earlier length from a later state recovers the earlier state. -/
theorem take_eq_of_le (state extra : ℕ → List R)
    (hstep : ∀ n, state (n + 1) = state n ++ extra n)
    {i j : ℕ} (h : i ≤ j) :
    (state j).take ((state i).length) = state i :=
  (List.prefix_iff_eq_take.mp (prefix_of_le state extra hstep h)).symm

/-- An existing entry has the same value at the same natural index at every
later time. The later index bound follows from the proved length inequality. -/
theorem getElem_eq_of_le (state extra : ℕ → List R)
    (hstep : ∀ n, state (n + 1) = state n ++ extra n)
    {i j t : ℕ} (h : i ≤ j) (ht : t < (state i).length) :
    (state j)[t]'(Nat.lt_of_lt_of_le ht (length_le_of_le state extra hstep h)) =
      (state i)[t]'ht :=
  ((prefix_of_le state extra hstep h).getElem ht).symm

end ReflexiveFixedPoints.ListRunPrefix

end OAI
