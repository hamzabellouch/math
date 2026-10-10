import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Resources
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Magnitudes
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OAI

/-! # An integer main-branch guard and the polynomial-bit promise

The guard uses the binary ceiling logarithm. It implies the manuscript's
real logarithmic guard and eventually passes for every fixed polynomial
bound on input bit length. Its stricter rounding only changes the fallback
on a finite initial range for each polynomial-bit promise.
-/

namespace LowSpaceSubsetSum

def mainGuard (N n u : ℕ) : Bool := decide (N ≤ n ∧ Nat.clog 2 u ≤ n / 1000000000)

theorem mainGuard_log {N n u : ℕ} (hu : 0 < u) (h : mainGuard N n u = true) :
    Real.logb 2 (u : ℝ) ≤ (n : ℝ) / 1000000000 := by
  have hc : Nat.clog 2 u ≤ n / 1000000000 := ((of_decide_eq_true h) :
    N ≤ n ∧ Nat.clog 2 u ≤ n / 1000000000).2
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hp : (u : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 u := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) u
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) huR hp
  have hbits : Real.logb 2 (u : ℝ) ≤ Nat.clog 2 u := by
    simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      mul_one] using hl
  have hh : 1000000000 * Nat.clog 2 u ≤ n := by omega
  have hhR : (1000000000 : ℝ) * Nat.clog 2 u ≤ n := by exact_mod_cast hh
  linarith only [hbits, hhR]

theorem eventually_mainGuard (N c : ℕ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ b : ℕ, b ≤ n ^ c → mainGuard N n (n + b + 2) = true := by
  filter_upwards [polynomial_absorption (c + 2)
    (by norm_num : (0 : ℝ) < 1 / 2000000000),
    Filter.eventually_ge_atTop N,
    Filter.eventually_ge_atTop 2000000000] with n hp hnN hn
  intro b hb
  have hn2 : 2 ≤ n := by omega
  have hu : n + b + 2 ≤ n ^ (c + 2) := by
    have h0 := polynomial_bit_bound hn2 hc hb
    have hsq : 3 ≤ n ^ 2 := by nlinarith
    have hm := Nat.mul_le_mul_right (n ^ c) hsq
    rw [pow_add]
    nlinarith only [h0, hm]
  have hfloor : (n : ℝ) / 2000000000 ≤ (n / 1000000000 : ℕ) := by
    have hdiv : n < 1000000000 * (n / 1000000000 + 1) := by omega
    have hdivR : (n : ℝ) < 1000000000 * ((n / 1000000000 : ℕ) + 1 : ℝ) := by
      exact_mod_cast hdiv
    have hnR : (2000000000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [hdivR, hnR]
  have hpow : n + b + 2 ≤ 2 ^ (n / 1000000000) := by
    have h1 : ((n + b + 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ (c + 2) := by exact_mod_cast hu
    have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hfloor
    have hp' : (n : ℝ) ^ (c + 2) ≤ (2 : ℝ) ^ ((n : ℝ) / 2000000000) := by
      simpa only [one_div_mul_eq_div] using hp
    have hh := h1.trans (hp'.trans h2)
    exact_mod_cast hh
  have hclog := Nat.clog_le_of_le_pow hpow
  exact decide_eq_true (show N ≤ n ∧ Nat.clog 2 (n + b + 2) ≤ n / 1000000000 from ⟨hnN, hclog⟩)

end LowSpaceSubsetSum

end OAI
