import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticNormRate
import OAI.NumberTheory.Ostmann.Characters.FourierWindowDecay
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # The frequency budget after return to the original prime law -/

namespace Ostmann
open Filter
open scoped SchwartzMap

theorem arithmetic_prime_page_spectator_cost (n m : ℕ) :
    ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) * 2 ^ (2 ^ n * m) =
      2 * Real.exp (Real.log 12 * (2 ^ n : ℕ) * m) := by
  have hbase : (2 : ℝ) * 3 * 2 = 12 := by norm_num
  calc
    _ = 2 * (((2 : ℝ) * 3 * 2) ^ (2 ^ n * m)) := by
      simp only [mul_pow]
      ring
    _ = _ := by
      rw [hbase]
      congr 1
      rw [show Real.log 12 * (2 ^ n : ℕ) * m =
        ((2 ^ n * m : ℕ) : ℝ) * Real.log 12 by push_cast; ring,
        Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 12)]

/-- The prime-cell mixture adds one factor two per bulk coordinate. This
changes the constant in the exponential from log six to log twelve. -/
theorem arithmetic_prime_norm_budget_rate (n : ℕ) (A C ε : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∃ D : ℝ, 0 ≤ D ∧
      (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * C * m) → (q.divisors.card : ℝ) ≤ D) ∧
      ∀ N V : ℕ, ∀ Δ : ℝ, (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      (A * Real.exp (-(2 ^ n : ℕ) * Δ)) *
        ((2 * Real.exp (Real.log 12 * (2 ^ n : ℕ) * m)) *
          ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
            (2 * (V : ℝ)) ^ (2 * 2 ^ n))) ≤
        Real.exp ((2 ^ n : ℕ) * Δ + Real.log 12 * (2 ^ n : ℕ) * m + ε * m) := by
  have hlog : Real.log 12 = Real.log 2 + Real.log 6 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (6 : ℝ) ≠ 0)]
    norm_num
  filter_upwards [arithmetic_norm_budget_rate n A C ε hA hC hε] with m hm
  obtain ⟨D, hD, hdiv, hcost⟩ := hm
  refine ⟨D, hD, hdiv, ?_⟩
  intro N V Δ hN hV
  have h := mul_le_mul_of_nonneg_left (hcost N V Δ hN hV)
    (Real.exp_pos (Real.log 2 * (2 ^ n : ℕ) * m)).le
  convert h using 1 <;> rw [hlog] <;>
    simp only [add_mul, Real.exp_add] <;> ring

/-- Specialization to the actual even bulk size, with the literal window and
Page/spectator constants of the prime norm estimate. -/
theorem arithmetic_prime_fourier_budget_rate (ψ : 𝓢(ℝ, ℂ)) (n k : ℕ) (hk : 0 < k)
    (B C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∃ D : ℝ, 0 ≤ D ∧
        (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * C * m) → (q.divisors.card : ℝ) ≤ D) ∧
        ∀ N V : ℕ, ∀ Δ : ℝ, (N : ℝ) ≤ Real.exp (C * m) →
        (V : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
        (((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
          B ^ (2 ^ n - 1)) ^ 2 *
          (((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
            ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
              (2 * (V : ℝ)) ^ (2 * 2 ^ n)))) * 2 ^ (2 ^ n * m) ≤
          Real.exp ((2 ^ n : ℕ) * Δ + Real.log 12 * (2 ^ n : ℕ) * m + ε * m) := by
  let A : ℝ := ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2
  have hrate := (spectatorBulkCount_tendsto k hk).eventually
    (arithmetic_prime_norm_budget_rate n A C ε (sq_nonneg _) hC hε)
  filter_upwards [hrate] with L hrate
  obtain ⟨D, hD, hdiv, hcost⟩ := hrate
  refine ⟨D, hD, hdiv, ?_⟩
  intro N V Δ hN hV
  have h := hcost N V Δ hN hV
  rw [← arithmetic_prime_page_spectator_cost n (spectatorBulkCount k L)] at h
  rw [fourier_window_pair_exp]
  exact le_trans (le_of_eq (by dsimp only [A]; ring)) h

end Ostmann

end OAI
