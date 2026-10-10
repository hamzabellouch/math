import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternCostRate
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticPrimeNormRate

namespace OAI

/-! # A depth-independent cost for all original equality patterns -/

namespace Ostmann
open Filter

/-- The original internal-prior cost has an absolute coefficient of `2^n m`
once the depth is chosen. The fixed pattern count is absorbed only as `L`
tends to infinity; no constant exponential in the depth is charged per slot. -/
theorem movingPattern_prior_cost_rate (k : ℕ) (hk : 0 < k)
    (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 < ε) (hdepth : 8 * C ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ, n ≤ k →
      (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
          (max 2 (Real.exp (C * L))) ^ (4 * n * 2 ^ n) ≤
        Real.exp ((2 ^ n : ℕ) * spectatorBulkCount k L + ε * spectatorBulkCount k L) := by
  let J := 4 * k * 2 ^ k
  let A : ℝ := (J ^ 2 : ℕ) * Real.log 2
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hm := (spectatorBulkCount_tendsto k hk).eventually
    (eventually_ge_atTop (A / ε))
  filter_upwards [hm, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (4 / (k : ℝ) ^ 4)] with L hm hL hscale n hn
  have hL0 : 0 ≤ L := by linarith
  have hscale' : 4 ≤ (k : ℝ) ^ 4 * L := by
    simpa only [mul_comm] using
      (div_le_iff₀ (by positivity : 0 < (k : ℝ) ^ 4)).mp hscale
  have hbulk := spectatorBulkCount_half k L hscale'
  have hsmall : A ≤ ε * spectatorBulkCount k L := by
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hm
  have hJ : 4 * n * 2 ^ n ≤ J := by
    dsimp only [J]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hn) (Nat.pow_le_pow_right (by decide) hn)
  have hcount : (((4 * n * 2 ^ n) ^ 2 : ℕ) : ℝ) * Real.log 2 ≤ A := by
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by norm_num))
    exact_mod_cast Nat.pow_le_pow_left hJ 2
  have hkc : 8 * C * (k : ℝ) ≤ (k : ℝ) ^ 4 := by
    calc
      _ ≤ (k : ℝ) ^ 3 * k := mul_le_mul_of_nonneg_right hdepth hkR.le
      _ = _ := by ring
  have hkcL := mul_le_mul_of_nonneg_right hkc hL0
  have hprior : 4 * (n : ℝ) * C * L ≤ (spectatorBulkCount k L : ℝ) := by
    have hnR : (n : ℝ) ≤ k := by exact_mod_cast hn
    have hnk := mul_le_mul_of_nonneg_right hnR (mul_nonneg (by linarith : 0 ≤ C) hL0)
    nlinarith
  have hprior' := mul_le_mul_of_nonneg_left hprior
    (show (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) by positivity)
  have hCL : 1 ≤ C * L := one_le_mul_of_one_le_of_one_le hC hL
  have he : (2 : ℝ) ≤ Real.exp (C * L) := by linarith [Real.add_one_le_exp (C * L)]
  rw [max_eq_right he, ← Real.exp_log (by norm_num : (0 : ℝ) < 2),
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast at hcount hprior' ⊢
  nlinarith

/-- The retained numerical norm, including all original equality-pattern
weights, has the absolute bulk constant `log 12 + 1`. -/
theorem arithmetic_prime_pattern_budget_rate (ψ : SchwartzMap ℝ ℂ) (n k : ℕ)
    (hk : 0 < k) (hn : n ≤ k) (B Cfreq Cprior ε : ℝ)
    (hCfreq : 0 ≤ Cfreq) (hCprior : 1 ≤ Cprior) (hε : 0 < ε)
    (hdepth : 8 * Cprior ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∃ D : ℝ, 0 ≤ D ∧
        (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * Cfreq * m) →
          (q.divisors.card : ℝ) ≤ D) ∧
        ∀ N V : ℕ, ∀ Δ : ℝ, (N : ℝ) ≤ Real.exp (Cfreq * m) →
        (V : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
        ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
          (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
          ((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
            B ^ (2 ^ n - 1)) ^ 2 *
            (((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * m)) *
              ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
                (2 * (V : ℝ)) ^ (2 * 2 ^ n)))) * 2 ^ (2 ^ n * m)) ≤
          Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) := by
  filter_upwards [movingPattern_prior_cost_rate k hk Cprior (ε / 4) hCprior
      (by positivity) hdepth,
    arithmetic_prime_fourier_budget_rate ψ n k hk B Cfreq (ε / 4) hCfreq (by positivity),
    (spectatorBulkCount_tendsto k hk).eventually (eventually_ge_atTop (2 / ε))]
    with L hprior hrate hm
  dsimp only
  obtain ⟨D, hD, hdiv, hcost⟩ := hrate
  refine ⟨D, hD, hdiv, ?_⟩
  intro N V Δ hN hV
  have hp := hprior n hn
  have hc := hcost N V Δ hN hV
  have htwo : (2 : ℝ) ≤ Real.exp ((ε / 2) * spectatorBulkCount k L) := by
    have hscale := (div_le_iff₀ hε).mp hm
    have he := Real.add_one_le_exp ((ε / 2) * spectatorBulkCount k L)
    nlinarith
  have hprod := mul_le_mul hp hc (by positivity) (Real.exp_nonneg _)
  have hmain := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)
  apply le_trans (le_of_eq (by ring)) hmain |>.trans
  apply (mul_le_mul_of_nonneg_right htwo (by positivity)).trans_eq
  simp only [← Real.exp_add]
  congr 1
  ring

end Ostmann

end OAI
