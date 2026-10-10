import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterDiscard
import OAI.NumberTheory.Ostmann.Construction.OriginalMomentBudget

namespace OAI

/-! # Numerical scales for common-center extraction -/

namespace Ostmann

open Filter

theorem commonCenter_log_budget (T : ℝ) (r H : ℕ)
    (hT : 1 ≤ T) (hr : 10 ≤ r)
    (hH : (H : ℝ) ≤ 2 * Real.exp ((r - 10 : ℕ) * T + T / 5)) :
    Real.log (2 * (H : ℝ)) < ((r + 1 : ℕ) : ℝ) * T := by
  have hr' : ((r - 10 : ℕ) : ℝ) = r - 10 := by
    rw [Nat.cast_sub hr]; norm_num
  by_cases hHz : H = 0
  · subst H
    simp only [Nat.cast_zero, mul_zero, Real.log_zero]
    positivity
  have hHpos : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hHz
  apply (Real.log_lt_iff_lt_exp (by positivity : 0 < 2 * (H : ℝ))).mpr
  have hf : (4 : ℝ) < Real.exp (54 * T / 5) := by
    linarith [Real.add_one_le_exp (54 * T / 5)]
  calc
    _ ≤ 4 * Real.exp ((r - 10 : ℕ) * T + T / 5) := by linarith
    _ < Real.exp (54 * T / 5) * Real.exp ((r - 10 : ℕ) * T + T / 5) :=
      mul_lt_mul_of_pos_right hf (Real.exp_pos _)
    _ = _ := by rw [← Real.exp_add, hr']; push_cast; congr 1; ring

theorem eventual_commonCenter_small_budget :
    ∀ᶠ T : ℝ in atTop, ∀ (J r : ℕ),
      (r : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) → (J : ℝ) ≤ Real.exp (T + 1) →
      2 * r * (J : ℝ) ≤ (Real.exp (3 * T / 5)) ^ 2 := by
  have hp := ((isLittleO_pow_exp_pos_mul_atTop 1 (show (0 : ℝ) < 1 / 5 by norm_num)).const_mul_left
    (4 * Real.exp 1)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with T hpoly hT J r hr hJ
  have hTpos : 0 < T := by linarith
  have hrT : (r : ℝ) ≤ 2 * T := hr.trans (by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT
      (show (3 / 5 : ℝ) ≤ 1 by norm_num))
  have hp' : 4 * Real.exp 1 * T ≤ Real.exp (T / 5) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 4 * Real.exp 1 * T),
      abs_of_pos (Real.exp_pos _), pow_one, one_mul, one_div, inv_mul_eq_div] using hpoly
  calc
    _ ≤ (2 * (2 * T)) * Real.exp (T + 1) := by gcongr
    _ = 4 * T * Real.exp (T + 1) := by ring
    _ = (4 * Real.exp 1 * T) * Real.exp T := by rw [Real.exp_add]; ring
    _ ≤ Real.exp (T / 5) * Real.exp T := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; norm_num; ring

theorem commonCenter_denominator_lt_primes (T : ℝ) (Amax p : ℕ)
    (hT : 3 ≤ T) (hA : (Amax : ℝ) ≤ 2 * Real.exp (T / 5))
    (hp : Real.exp T ≤ (p : ℝ)) : Amax < p := by
  have hf : (2 : ℝ) < Real.exp (4 * T / 5) := by linarith [Real.add_one_le_exp (4 * T / 5)]
  have hh : (Amax : ℝ) < p := calc
    _ ≤ 2 * Real.exp (T / 5) := hA
    _ < Real.exp (4 * T / 5) * Real.exp (T / 5) := mul_lt_mul_of_pos_right hf (Real.exp_pos _)
    _ = Real.exp T := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ p := hp
  exact_mod_cast hh

theorem commonCenter_relative_size (T K J R Amax : ℝ) (k : ℕ)
    (hT : 30 ≤ T) (hK : K ≤ T) (hJ : 0 < J) (hR : 0 ≤ R)
    (hA : 0 < Amax) (hAU : Amax ≤ 2 * Real.exp (T / 5)) (hk : 0 < k)
    (hmoment : Real.exp (-K / 5) * J ^ (k + 1) / (4 * Amax) ≤ 2 * J * R ^ k) :
    J * Real.exp (-T / k) ≤ R := by
  have hfactor : (16 : ℝ) ≤ Real.exp (4 * T / 5 - K / 5) := by
    linarith [Real.add_one_le_exp (4 * T / 5 - K / 5)]
  have hcost : 8 * Amax ≤ Real.exp (-K / 5) * Real.exp T := by
    calc
      _ ≤ 16 * Real.exp (T / 5) := by linarith
      _ ≤ Real.exp (4 * T / 5 - K / 5) * Real.exp (T / 5) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hm := (div_le_iff₀ (show 0 < 4 * Amax by positivity)).mp hmoment
  have hh : J ^ k ≤ Real.exp T * R ^ k := by
    have hc := mul_le_mul_of_nonneg_right hcost (mul_nonneg hJ.le (pow_nonneg hR k))
    rw [pow_succ] at hm
    have hpos : 0 < Real.exp (-K / 5) * J := by positivity
    nlinarith only [hm, hc, hpos]
  have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_nonneg (-T))
  have hcanc : (Real.exp T * R ^ k) * Real.exp (-T) = R ^ k := by
    rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [hcanc] at hh'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpow : (J * Real.exp (-T / k)) ^ k = J ^ k * Real.exp (-T) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    field_simp
  apply le_of_pow_le_pow_left₀ hk.ne' hR
  rwa [hpow]

end Ostmann

end OAI
