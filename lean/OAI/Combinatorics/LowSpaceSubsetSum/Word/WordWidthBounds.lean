import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Magnitudes
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionSurvival

namespace OAI

/-! # Fixed word widths, watchdog counters and memory addresses

These are arithmetic bounds on the manuscript's concrete finite cutoffs.
They do not assert that the algorithm has been compiled to a RAM program.
-/

noncomputable section

namespace LowSpaceSubsetSum

def wordWidth {n : ℕ} (I : Instance n) : ℕ := 4 * inputScale I

def trialWatchdog {n : ℕ} (I : Instance n) : ℕ :=
  inputScale I ^ 500 * 2 ^ ((n + 1) / 2)

def writableWordLimit {n : ℕ} (I : Instance n) : ℕ :=
  inputScale I ^ 15 * compressionDictionaryCapacity n

theorem guarded_polynomial_exponential {n : ℕ} {u a : ℝ} (hn : 10000 ≤ n)
    (hu : 0 < u) (hlog : Real.logb 2 u ≤ (n : ℝ) / 1000000000)
    (k : ℕ) (hmargin : (k : ℝ) / 1000000000 + a ≤ 9 / 10) :
    u ^ k * (2 : ℝ) ^ (a * n + 1) < (2 : ℝ) ^ n := by
  have hp : u ^ k = (2 : ℝ) ^ ((k : ℝ) * Real.logb 2 u) := by
    have hh := Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) (Real.logb 2 u) k
    rw [Real.rpow_logb (by norm_num) (by norm_num) hu] at hh
    simpa only [mul_comm] using hh.symm
  rw [hp, ← Real.rpow_add (by norm_num), ← Real.rpow_natCast]
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hk := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k (α := ℝ))
  have hm := mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg n (α := ℝ))
  nlinarith only [hk, hm, hnR]

theorem trialWatchdog_lt_two_pow {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000) :
    trialWatchdog I < 2 ^ n := by
  have hu : (0 : ℝ) < inputScale I := by
    exact_mod_cast (show 0 < inputScale I by unfold inputScale; omega)
  have he : (((n + 1) / 2 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * n + 1 := by
    have hh : 2 * ((n + 1) / 2) ≤ n + 1 := by omega
    have hhR : (2 : ℝ) * ((n + 1) / 2 : ℕ) ≤ n + 1 := by exact_mod_cast hh
    linarith only [hhR]
  have hh := guarded_polynomial_exponential hn hu hlog 500
    (a := (1 / 2 : ℝ)) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he)
    (show 0 ≤ (inputScale I : ℝ) ^ 500 by positivity)
  have hcast : (trialWatchdog I : ℝ) < (2 : ℝ) ^ n := by
    simpa only [trialWatchdog, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Real.rpow_natCast] using hm.trans_lt hh
  exact_mod_cast hcast

theorem writableWordLimit_lt_two_pow {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000) :
    writableWordLimit I < 2 ^ n := by
  have hu : (0 : ℝ) < inputScale I := by
    exact_mod_cast (show 0 < inputScale I by unfold inputScale; omega)
  have he : ((199 * n / 1000 : ℕ) : ℝ) ≤ (199 / 1000 : ℝ) * n + 1 := by
    have hh : 1000 * (199 * n / 1000) ≤ 199 * n := by omega
    have hhR : (1000 : ℝ) * (199 * n / 1000 : ℕ) ≤ 199 * n := by exact_mod_cast hh
    linarith only [hhR]
  have hh := guarded_polynomial_exponential hn hu hlog 15
    (a := (199 / 1000 : ℝ)) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he)
    (show 0 ≤ (inputScale I : ℝ) ^ 15 by positivity)
  have hcast : (writableWordLimit I : ℝ) < (2 : ℝ) ^ n := by
    simpa only [writableWordLimit, compressionDictionaryCapacity, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast] using hm.trans_lt hh
  exact_mod_cast hcast

theorem cutoff_fits_word {n : ℕ} (I : Instance n) {x : ℕ} (hx : x < 2 ^ n) :
    x < 2 ^ wordWidth I := by
  apply hx.trans_le
  apply Nat.pow_le_pow_right (by decide)
  unfold wordWidth inputScale
  omega

end LowSpaceSubsetSum

end

end OAI
