import OAI.NumberTheory.Ostmann.QuadraticCenter.DyadicKernelShells

namespace OAI

/-! # The number of dyadic shells is negligible at the kernel scale -/

namespace Ostmann

open Filter Asymptotics

theorem dyadic_shell_count_bound (C T : ℝ) (hC : 0 ≤ C) (hT : 1 ≤ T)
    (M : ℕ) (hM : (M : ℝ) ≤ Real.exp (C * T)) :
    (Nat.log 2 M + 1 : ℝ) ≤ (2 + C / Real.log 2) * T := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hM0 : M = 0
  · subst M
    simp only [Nat.log_zero_right, Nat.cast_zero, zero_add]
    have hdiv : 0 ≤ C / Real.log 2 := div_nonneg hC hl2.le
    nlinarith
  · have hp : (2 : ℝ) ^ (Nat.log 2 M) ≤ M := by exact_mod_cast Nat.pow_log_le_self 2 hM0
    have hlog : (Nat.log 2 M : ℝ) * Real.log 2 ≤ C * T := by
      calc
        _ = Real.log ((2 : ℝ) ^ (Nat.log 2 M)) := (Real.log_pow _ _).symm
        _ ≤ Real.log M := Real.log_le_log (by positivity) hp
        _ ≤ C * T := (Real.log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hM0)).mpr hM
    have hh : (Nat.log 2 M : ℝ) ≤ (C / Real.log 2) * T := by
      apply (le_div_iff₀ hl2).mpr at hlog
      convert hlog using 1
      ring
    linarith

theorem eventual_dyadic_shell_budget (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ M : ℕ, (M : ℝ) ≤ Real.exp (C * T) →
      (Nat.log 2 M + 1 : ℝ) ≤ Real.exp (ε * T ^ (9999999 / 10000000 : ℝ)) := by
  let D := 2 + C / Real.log 2
  have hD : 1 ≤ D := by
    have : 0 ≤ C / Real.log 2 := div_nonneg hC (Real.log_pos (by norm_num)).le
    dsimp [D]
    linarith
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hκ : (0 : ℝ) < 9999999 / 10000000 := by norm_num
  have hl := (isLittleO_log_rpow_atTop hκ).bound (show 0 < ε / 2 by positivity)
  have hp := (tendsto_rpow_atTop hκ).eventually_ge_atTop (2 * Real.log D / ε)
  filter_upwards [hl, hp, eventually_ge_atTop (1 : ℝ)] with T hlog hpow hT M hM
  apply (dyadic_shell_count_bound C T hC hT M hM).trans
  apply (Real.log_le_iff_le_exp (mul_pos hD0 (by linarith))).mp
  rw [Real.log_mul hD0.ne' (by linarith : T ≠ 0)]
  have hh : Real.log T ≤ ε / 2 * T ^ (9999999 / 10000000 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hT),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ T) _)] using hlog
  have hc := (div_le_iff₀ hε).mp hpow
  linarith

end Ostmann

end OAI
