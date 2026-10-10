import OAI.NumberTheory.Ostmann.Construction.OriginalParameterChoice

namespace OAI

/-! # The concrete choices meet the local scale inequalities -/

namespace Ostmann

open Filter

theorem eventual_original_local_scales :
    ∀ᶠ V : ℝ in atTop, ∀ L : ℝ,
      V ^ (8 / 5 : ℝ) / 2 ≤ L → L ≤ (9 / 5 : ℝ) * V ^ (8 / 5 : ℝ) →
      V ^ (3 / 2 : ℝ) ≤ L ∧ L ≤ 2 * V ^ 2 ∧ 13 * V ≤ L ∧
      V ^ (3 / 5 : ℝ) / 2 ≤ (originalMomentOrder L V : ℝ) ∧
      (originalMomentOrder L V : ℝ) ≤ 2 * V ^ (3 / 5 : ℝ) ∧
      (originalMomentOrder L V : ℝ) * Real.log 2 ≤ V ∧
      1 ≤ originalHolderOrder V ∧
      V ^ (1 / 1000000 : ℝ) / 2 ≤ (originalHolderOrder V : ℝ) ∧
      (originalHolderOrder V : ℝ) ≤ V ^ (1 / 1000000 : ℝ) := by
  filter_upwards [(tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).eventually_ge_atTop 2,
    (tendsto_rpow_atTop (show (0 : ℝ) < 2 / 5 by norm_num)).eventually_ge_atTop 4,
    (tendsto_rpow_atTop (show (0 : ℝ) < 3 / 5 by norm_num)).eventually_ge_atTop 60,
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 1000000 by norm_num)).eventually_ge_atTop 2,
    eventually_ge_atTop (1 : ℝ)] with V h10 h25 h35 hμ hV L hLlo hLhi
  have hVp : 0 < V := by linarith
  have hsize := originalMomentOrder_size L V hVp hLlo hLhi h35
  have hholder := originalHolderOrder_bounds V hVp.le hμ
  have hpow32 : V ^ (8 / 5 : ℝ) = V ^ (3 / 2 : ℝ) * V ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_add hVp]; congr 1; norm_num
  have hpow1 : V ^ (8 / 5 : ℝ) = V * V ^ (3 / 5 : ℝ) := by
    rw [show (8 / 5 : ℝ) = 1 + 3 / 5 by norm_num, Real.rpow_add hVp, Real.rpow_one]
  have hpow2 : V ^ (8 / 5 : ℝ) ≤ V ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hV (show (8 / 5 : ℝ) ≤ 2 by norm_num)
  have hpowlog : V = V ^ (3 / 5 : ℝ) * V ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_add hVp, show (3 / 5 : ℝ) + 2 / 5 = 1 by norm_num, Real.rpow_one]
  have h32 : V ^ (3 / 2 : ℝ) ≤ L := by
    have hm := mul_le_mul_of_nonneg_left h10 (Real.rpow_nonneg hVp.le (3 / 2 : ℝ))
    rw [← hpow32] at hm
    linarith
  have h13 : 13 * V ≤ L := by
    have hm := mul_le_mul_of_nonneg_left h35 hVp.le
    rw [← hpow1] at hm
    linarith
  have hlog : (originalMomentOrder L V : ℝ) * Real.log 2 ≤ V := by
    have hlog2 : Real.log (2 : ℝ) ≤ 2 := Real.log_le_self (by norm_num)
    have hm := mul_le_mul_of_nonneg_left h25 (Real.rpow_nonneg hVp.le (3 / 5 : ℝ))
    rw [← hpowlog] at hm
    have hk := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (originalMomentOrder L V))
    nlinarith only [hm, hk, hsize.2]
  exact ⟨h32, by nlinarith, h13, hsize.1, hsize.2, hlog, hholder.1, hholder.2.1, hholder.2.2⟩

theorem eventual_originalMomentOrder_population (C : ℝ) (hC : 0 < C) :
    ∀ᶠ V : ℝ in atTop, ∀ (L : ℝ) (J : ℕ),
      V ^ (8 / 5 : ℝ) / 2 ≤ L → L ≤ (9 / 5 : ℝ) * V ^ (8 / 5 : ℝ) →
      Real.exp V ≤ C * V * J → 2 * (originalMomentOrder L V) ^ 2 ≤ J := by
  have hpoly := ((isLittleO_pow_exp_pos_mul_atTop 3 (show (0 : ℝ) < 1 by norm_num)).const_mul_left
    (8 * C)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hpoly, eventual_original_local_scales, eventually_ge_atTop (1 : ℝ)]
    with V hpoly hsc hV L J hLlo hLhi hpop
  have hnum : 8 * C * V ^ 3 ≤ Real.exp V := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (8 * C) * V ^ 3),
      one_mul, abs_of_pos (Real.exp_pos _)] using hpoly
  have hJ : 8 * V ^ 2 ≤ (J : ℝ) := by
    have hp := hnum.trans hpop
    have hCV : 0 < C * V := mul_pos hC (by linarith)
    apply (mul_le_mul_iff_left₀ hCV).mp
    nlinarith only [hp]
  have hk := (hsc L hLlo hLhi).2.2.2.2.1
  have hpow : V ^ (3 / 5 : ℝ) ≤ V := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hV (show (3 / 5 : ℝ) ≤ 1 by norm_num)
  have hkV : (originalMomentOrder L V : ℝ) ≤ 2 * V := by linarith
  have hk0 : (0 : ℝ) ≤ originalMomentOrder L V := Nat.cast_nonneg _
  have hh : 2 * (originalMomentOrder L V : ℝ) ^ 2 ≤ (J : ℝ) := by nlinarith
  exact_mod_cast hh

end Ostmann

end OAI
