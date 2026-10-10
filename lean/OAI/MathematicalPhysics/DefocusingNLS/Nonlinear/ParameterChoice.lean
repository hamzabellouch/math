import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

namespace OAI

/-!
# Finite choices of the nonlinearity power and Sobolev index

The manuscript first constructs profiles for all sufficiently small positive
`a`, then chooses an odd integer power with `a = 1 / (p - 1)`, and only afterward
chooses the finite Sobolev index. These lemmas justify that order of choices.
-/

namespace DefocusingNLS

/-- Every small-parameter interval contains the reciprocal of an even positive
integer, yielding an odd power at least three. -/
theorem exists_odd_power_with_small_reciprocal (a₀ : ℝ) (ha₀ : 0 < a₀) :
    ∃ p : ℕ, Odd p ∧ 3 ≤ p ∧ 0 < 1 / ((p : ℝ) - 1) ∧
      1 / ((p : ℝ) - 1) < a₀ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / a₀)
  have hden : 0 < ((2 * n + 3 : ℕ) : ℝ) - 1 := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨2 * n + 3, ⟨n + 1, by omega⟩, by omega, one_div_pos.mpr hden, ?_⟩
  apply (div_lt_iff₀ hden).mpr
  have hlarge : 1 / a₀ < ((2 * n + 3 : ℕ) : ℝ) - 1 := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hmul := (div_lt_iff₀ ha₀).mp hlarge
  nlinarith

/-- The high derivative index can be chosen after the profile and potential
bound, without an infinite regularity requirement. -/
theorem exists_sobolev_index (a B : ℝ) :
    ∃ k : ℕ, 8 < k ∧ 6 - 2 * a + 2 * B + 1 < (k : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 8 (6 - 2 * a + 2 * B + 1))
  refine ⟨k, ?_, lt_of_le_of_lt (le_max_right _ _) hk⟩
  have h8 : (8 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  exact_mod_cast h8

/-- Every power considered here is energy-supercritical in dimension twelve. -/
theorem energy_supercritical_in_twelve {p : ℕ} (hp : 3 ≤ p) :
    1 < 6 - 2 / ((p : ℝ) - 1) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hd : 0 < (p : ℝ) - 1 := by linarith
  have hdiv : 2 / ((p : ℝ) - 1) ≤ 1 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  linarith

end DefocusingNLS

end OAI
