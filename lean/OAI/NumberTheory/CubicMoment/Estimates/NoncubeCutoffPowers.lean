import OAI.NumberTheory.CubicMoment.Estimates.PrimeExclusionSavingPowers
import OAI.NumberTheory.CubicMoment.Estimates.CoreBlockGeometry

namespace OAI

/-! Numerical margins for the three actual noncube conductor regions. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma low_core_log_threshold (A : ℕ) :
    ∀ᶠ L : ℝ in atTop, 5832*(1+Real.log L)^A ≤ (Real.log L)^(A+1) := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop
    (max 1 (5832*(2:ℝ)^A))] with L hL
  have hlog : 1 ≤ Real.log L := (le_max_left _ _).trans hL
  have hlarge : 5832*(2:ℝ)^A ≤ Real.log L := (le_max_right _ _).trans hL
  calc
    _ ≤ 5832*(2*Real.log L)^A := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) (by linarith) _) (by norm_num)
    _ = (5832*(2:ℝ)^A)*(Real.log L)^A := by rw [mul_pow]; ring
    _ ≤ Real.log L*(Real.log L)^A := mul_le_mul_of_nonneg_right hlarge (pow_nonneg (by linarith) _)
    _ = _ := by rw [pow_succ]; ring

lemma low_height_power_threshold (U : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ u : ℝ, |u| ≤ (1+Real.log L)^U →
      1+|u| ≤ L^(9/25:ℝ) := by
  have h := exclusion_log_absorption (c := (9/25:ℝ)) (d := 0) (ε := 1)
    (by norm_num) (by norm_num) (C := 2) (by norm_num) U 0
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with L h hL
  have hp := h (L^(9/25:ℝ)) 1 (by norm_num) (by simp) le_rfl
  simp only [Real.one_rpow,mul_one,pow_zero,div_one] at hp
  intro u hu
  have hz : 1 ≤ (1+Real.log L)^U := one_le_pow₀ (by linarith [Real.log_nonneg hL])
  linarith

lemma small_core_ordinary_window {L U V : ℝ} (hL : 0 ≤ L) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hsmall : U*V^2 ≤ L^(1/4:ℝ)) (hmargin : 16*L^(1/2:ℝ) ≤ L) :
    (4*U*V)^2 ≤ L := by
  have hUV : U*V ≤ U*V^2 := by
    have hvv : V ≤ V^2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hvv (by linarith)
  have he : (L^(1/4:ℝ))^2 = L^(1/2:ℝ) := by
    rw [← Real.rpow_natCast _ 2,← Real.rpow_mul hL]
    norm_num
  calc
    _ = 16*(U*V)^2 := by ring
    _ ≤ 16*(L^(1/4:ℝ))^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (hUV.trans hsmall) 2) (by norm_num)
    _ = 16*L^(1/2:ℝ) := by rw [he]
    _ ≤ L := hmargin

end CubicFirstMoment

end

end OAI
