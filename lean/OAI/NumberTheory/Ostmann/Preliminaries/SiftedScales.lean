import OAI.NumberTheory.Ostmann.Preliminaries.SiftedModuli

namespace OAI

open Erdos970

namespace Ostmann.SiftedWeights
open Filter

def sieveLevel (n : ℕ) : ℕ := 2^n

def smallPrimeCutoff (j n : ℕ) : ℕ := 2^(n/(10*j))

theorem eventually_sieve_scales (j K : ℕ) (hj : 0 < j) :
    ∀ᶠ n : ℕ in atTop,
      max K 2 ≤ smallPrimeCutoff j n ∧ 1 < sieveLevel n ∧
      (j : ℝ)*(Real.log (smallPrimeCutoff j n : ℝ)+(Real.log 4+4)) ≤
        Real.log (sieveLevel n : ℝ)/2 ∧
      Real.log (sieveLevel n : ℝ)/(20*(j : ℝ)) ≤
        Real.log (smallPrimeCutoff j n : ℝ) := by
  have hjr : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨R, hR⟩ := exists_nat_ge (10*(j : ℝ)*(Real.log 4+4)/Real.log 2)
  filter_upwards [eventually_ge_atTop (10*j*(K+1)), eventually_ge_atTop R] with n hn hnR
  have hd : 0 < 10*j := by omega
  have hq : K+1 ≤ n/(10*j) := (Nat.le_div_iff_mul_le hd).mpr (by nlinarith)
  have hn1 : 1 ≤ n := by nlinarith
  have hcut : max K 2 ≤ smallPrimeCutoff j n := by
    have hh := (Nat.lt_two_pow_self : n/(10*j) < 2^(n/(10*j)))
    dsimp [smallPrimeCutoff]
    omega
  have hlevel : 1 < sieveLevel n := by
    have hh := (Nat.lt_two_pow_self : n < 2^n)
    dsimp [sieveLevel]
    omega
  have hNlog : Real.log (smallPrimeCutoff j n : ℝ) = (n/(10*j) : ℕ)*Real.log 2 := by
    simp [smallPrimeCutoff, Nat.cast_pow, Real.log_pow]
  have hQlog : Real.log (sieveLevel n : ℝ) = (n : ℝ)*Real.log 2 := by
    simp [sieveLevel, Nat.cast_pow, Real.log_pow]
  have hdiv : (n/(10*j) : ℕ)*(10*j) ≤ n := Nat.div_mul_le_self n (10*j)
  have hdivr : ((n/(10*j) : ℕ) : ℝ)*(10*(j : ℝ)) ≤ n := by exact_mod_cast hdiv
  have hscaled := mul_le_mul_of_nonneg_right hdivr hlog.le
  have hnr : 10*(j : ℝ)*(Real.log 4+4)/Real.log 2 ≤ (n : ℝ) :=
    hR.trans (by exact_mod_cast hnR)
  have hmain := (div_le_iff₀ hlog).mp hnr
  have hquot : n ≤ 2*(n/(10*j))*(10*j) := by
    have hrem := Nat.mod_lt n hd
    have hid := Nat.mod_add_div n (10*j)
    have hq1 : 1 ≤ n/(10*j) := by omega
    have hqmul : 10*j ≤ (n/(10*j))*(10*j) := Nat.le_mul_of_pos_left _ hq1
    nlinarith
  have hquotr : (n : ℝ) ≤ 2*((n/(10*j) : ℕ) : ℝ)*(10*(j : ℝ)) := by
    exact_mod_cast hquot
  refine ⟨hcut, hlevel, ?_, ?_⟩
  · rw [hNlog, hQlog]
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hlog.le]
  · rw [hNlog, hQlog, div_le_iff₀ (by positivity : 0 < 20*(j : ℝ))]
    have := mul_le_mul_of_nonneg_right hquotr hlog.le
    nlinarith

end Ostmann.SiftedWeights

end OAI
