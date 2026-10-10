import OAI.NumberTheory.Ostmann.Statement

namespace OAI

namespace Ostmann.SiftedWeights
open Filter

theorem dyadic_bound_to_log_bound (f : ℕ → ℝ) (hf : Monotone f)
    (hpos : ∀ x, 0 ≤ f x) (j : ℕ)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      f (4^n) ≤ C*(4 : ℝ)^n/(n : ℝ)^j) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      f x ≤ C*x/(Real.log (x : ℝ))^j := by
  obtain ⟨C, hC, hevent⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨4*C*(Real.log 4)^j, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (4^N), eventually_ge_atTop 2] with x hxN hx2
  let n := Nat.log 4 x+1
  have hnN : N ≤ n := (Nat.le_log_of_pow_le (by norm_num) hxN).trans (Nat.le_succ _)
  have hn1 : 0 < n := by dsimp [n]; omega
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hxlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hxpow : x ≤ 4^n := (Nat.lt_pow_succ_log_self (by norm_num) x).le
  have hpowx : (4 : ℝ)^n ≤ 4*(x : ℝ) := by
    have hp := Nat.pow_log_le_self 4 (show x ≠ 0 by omega)
    have hpr : (4 : ℝ)^(Nat.log 4 x) ≤ x := by exact_mod_cast hp
    dsimp [n]
    rw [pow_succ]
    nlinarith
  have hfx : f x ≤ C*(4 : ℝ)^n/(n : ℝ)^j := (hf hxpow).trans (hN n hnN)
  have hfxmul := (le_div_iff₀ (pow_pos hnreal j)).mp hfx
  have hlog : Real.log (x : ℝ) ≤ (n : ℝ)*Real.log 4 := by
    have hp : (x : ℝ) ≤ (4 : ℝ)^n := by exact_mod_cast hxpow
    simpa only [Real.log_pow] using Real.log_le_log hxpos hp
  have hlogpow := pow_le_pow_left₀ hxlog.le hlog j
  rw [mul_pow] at hlogpow
  have hchain : f x*(Real.log (x : ℝ))^j ≤ (C*(4*(x : ℝ)))*(Real.log 4)^j := by
    calc
      f x*(Real.log (x : ℝ))^j ≤ f x*((n : ℝ)^j*(Real.log 4)^j) :=
        mul_le_mul_of_nonneg_left hlogpow (hpos x)
      _ = (f x*(n : ℝ)^j)*(Real.log 4)^j := by ring
      _ ≤ (C*(4 : ℝ)^n)*(Real.log 4)^j :=
        mul_le_mul_of_nonneg_right hfxmul (pow_nonneg hlog4.le j)
      _ ≤ (C*(4*(x : ℝ)))*(Real.log 4)^j :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpowx hC.le) (pow_nonneg hlog4.le j)
  apply (le_div_iff₀ (pow_pos hxlog j)).mpr
  convert hchain using 1; ring

theorem eventually_boundary_negligible (j K : ℕ) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ)^n+K+1 ≤ (4 : ℝ)^n/(n : ℝ)^j := by
  have hK : (0 : ℝ) < K+2 := by positivity
  have ht := tendsto_pow_const_div_const_pow_of_one_lt j (r := (2 : ℝ)) (by norm_num)
  have he := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1/(K+2 : ℝ) by positivity))
  filter_upwards [he, eventually_ge_atTop 1] with n hn hn1
  have hp : (0 : ℝ) < (2 : ℝ)^n := by positivity
  have hp1 : (1 : ℝ) ≤ (2 : ℝ)^n := one_le_pow₀ (by norm_num)
  have hnp : (0 : ℝ) < (n : ℝ)^j := pow_pos (by exact_mod_cast hn1) j
  have hb : (2 : ℝ)^n+K+1 ≤ (K+2 : ℝ)*(2 : ℝ)^n := by
    have := mul_nonneg (show (0 : ℝ) ≤ K+1 by positivity) (sub_nonneg.mpr hp1)
    nlinarith
  have hr := (div_lt_div_iff₀ hp hK).mp hn
  have hmul := mul_le_mul_of_nonneg_right hr.le hp.le
  have heq : (2 : ℝ)^n*(2 : ℝ)^n = (4 : ℝ)^n := by rw [← mul_pow]; norm_num
  rw [one_mul, heq] at hmul
  apply (le_div_iff₀ hnp).mpr
  have hh := mul_le_mul_of_nonneg_right hb hnp.le
  nlinarith

end Ostmann.SiftedWeights

end OAI
