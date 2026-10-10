import Mathlib

namespace OAI

/-!
# Finite dependency-path accounting

The double sum is the dependency-path budget in Section 10 of the
edit-distance manuscript, with separate branching bounds for same-index
and earlier-index requests.
-/

namespace EditApproximation

open Finset

/-- Overcount of dependency paths with at most `depth` descending edges
and `indices` strictly earlier-index/pass edges. -/
def dependencyPathBudget (depth indices same earlier : ℕ) : ℕ :=
  ∑ r ∈ range (depth + 1), ∑ s ∈ range (indices + 1),
    (r + s).choose r * same ^ r * earlier ^ s

/-- Explicit bound on the double sum, before substituting asymptotic
parameters. All quantities are natural numbers. -/
theorem dependencyPathBudget_le (depth indices same earlier : ℕ)
    (hsame : 1 ≤ same) (hearlier : 1 ≤ earlier) :
    dependencyPathBudget depth indices same earlier ≤
      (depth + 1) * (indices + 1) * 2 ^ (depth + indices) *
        same ^ depth * earlier ^ indices := by
  let bound := 2 ^ (depth + indices) * same ^ depth * earlier ^ indices
  have hterm (r s : ℕ) (hr : r ≤ depth) (hs : s ≤ indices) :
      (r + s).choose r * same ^ r * earlier ^ s ≤ bound := by
    have hchoose := (Nat.choose_le_two_pow (r + s) r).trans
      (pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) (Nat.add_le_add hr hs))
    exact Nat.mul_le_mul (Nat.mul_le_mul hchoose (pow_le_pow_right' hsame hr))
      (pow_le_pow_right' hearlier hs)
  have hsum : dependencyPathBudget depth indices same earlier ≤
      ∑ _r ∈ range (depth + 1), ∑ _s ∈ range (indices + 1), bound := by
    apply sum_le_sum
    intro r hr
    apply sum_le_sum
    intro s hs
    exact hterm r s (by simpa using mem_range.mp hr) (by simpa using mem_range.mp hs)
  apply hsum.trans_eq
  simp only [sum_const, card_range, smul_eq_mul, bound]
  ring

end EditApproximation

end OAI
