import Mathlib

namespace OAI

/-! Uniform eventual smallness used to absorb the constant loss in the odd
low-degree estimate.  The threshold is independent of the factor degree and
of the particular parameter `q` below its stated envelope. -/

open Filter

namespace Problem335

/-- A polynomially decaying envelope absorbs every fixed positive power
and fixed nonnegative multiplicative constant, uniformly below the envelope. -/
theorem eventually_small_power_of_envelope (a b C : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℝ, 0 ≤ q →
      q ≤ (n : ℝ) ^ (-a) → C * q ^ b ≤ 1 := by
  have hlim : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(a * b)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (mul_pos ha hb)).comp
        tendsto_natCast_atTop_atTop)
  have hevent : ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ (-(a * b)) < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨N, ?_⟩
  intro n hn q hq henv
  calc
    C * q ^ b ≤ C * ((n : ℝ) ^ (-a)) ^ b :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq henv hb.le) hC
    _ = C * (n : ℝ) ^ (-(a * b)) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg n)]
      congr 2
      ring
    _ ≤ 1 := (hN n hn).le

/-- The exact eventual smallness hypothesis used for all low odd degrees. -/
theorem eventually_odd_degree_smallness :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℝ, 0 ≤ q →
      q ≤ (n : ℝ) ^ (-(2 / 5 : ℝ)) →
      5 * q ^ (3 / 16 : ℝ) ≤ 1 := by
  exact eventually_small_power_of_envelope (2 / 5) (3 / 16) 5
    (by norm_num) (by norm_num) (by norm_num)

end Problem335

end OAI
