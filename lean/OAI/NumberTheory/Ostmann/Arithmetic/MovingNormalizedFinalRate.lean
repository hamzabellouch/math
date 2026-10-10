import OAI.NumberTheory.Ostmann.Arithmetic.MovingFinalRate

namespace OAI

/-! # The final numerical contradiction retains both giant normalizers -/
namespace Ostmann
open Filter

theorem moving_normalized_amplitude_lower (B r m cg : ℝ) (η statistic : ℂ)
    (hloss : 2 * cg ≤ r * m)
    (hid : η = (Real.exp (2 * cg) : ℂ) * statistic)
    (hlower : Real.exp (-B * r * m) ≤ ‖η‖) :
    Real.exp (-(B + 1) * r * m) ≤ ‖statistic‖ := by
  rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)] at hlower
  have h := mul_le_mul_of_nonneg_left hlower (Real.exp_nonneg (-2 * cg))
  have hinv : Real.exp (-2 * cg) * Real.exp (2 * cg) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hs : Real.exp (-2 * cg + -B * r * m) ≤ ‖statistic‖ := by
    calc
      _ = Real.exp (-2 * cg) * Real.exp (-B * r * m) := Real.exp_add _ _
      _ ≤ Real.exp (-2 * cg) * (Real.exp (2 * cg) * ‖statistic‖) := h
      _ = _ := by rw [← mul_assoc, hinv, one_mul]
  exact (Real.exp_le_exp.mpr (by nlinarith only [hloss])).trans hs

theorem eventually_moving_normalized_numeric_contradiction (Bs BD Bz B C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop, ∀ᶠ L : ℝ in atTop,
      let m := spectatorBulkCount k L
      let r : ℝ := (2 : ℝ) ^ k
      let A := movingFrequencyRate Bs BD Bz ((k : ℝ) ^ 4) k
      let D := Bs + 8 * Real.log ((k : ℝ) ^ 4)
      ∀ V : ℕ, (V : ℝ) ≤ Real.exp (A * m) → 0 ≤ A →
      ∀ Δ cg : ℝ, Δ ≤ D * m → cg ≤ L → ∀ η statistic : ℂ,
      η = (Real.exp (2 * cg) : ℂ) * statistic →
      Real.exp (-B * r * m) ≤ ‖η‖ →
      ‖statistic‖ ^ 2 ≤ C * (2 * V + 1 : ℕ) * Real.exp 5 *
        (4 * ((((2 ^ k + 1) * (2 ^ k) ^ (2 * 2 ^ k) : ℕ) : ℝ) *
          Real.exp (r * m * (-(3 / 4 : ℝ) * Real.log ((2 : ℝ) ^ k) + 5 / 4)) *
            (Real.exp (r * Δ + (Real.log 12 + 1) * r * m + m) +
              5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
          Real.exp (-(A + (2 * (B + 1) + 1) * r + 1) * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)))) → False := by
  filter_upwards [eventually_moving_numeric_contradiction Bs BD Bz (B + 1)
    (4 * C * Real.exp 3) (by positivity), eventually_ge_atTop (2 : ℕ)] with k hk hk2
  filter_upwards [hk, eventually_ge_atTop (1 : ℝ)] with L hfinal hL
  dsimp only at hfinal ⊢
  intro V hV hA Δ cg hΔ hcg η statistic hid hlower hupper
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hk4 : (16 : ℝ) ≤ (k : ℝ) ^ 4 := by
    convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hkR 4 using 1
    norm_num
  have hm := spectatorBulkCount_lower k L
  have hr : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hloss : 2 * cg ≤ (2 : ℝ) ^ k * spectatorBulkCount k L := by
    have hm2 : 2 * L ≤ (spectatorBulkCount k L : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right hk4 (show 0 ≤ L by linarith)]
    have hrm := mul_le_mul_of_nonneg_right hr (show 0 ≤ (spectatorBulkCount k L : ℝ) by positivity)
    nlinarith
  apply hfinal V hV hA Δ hΔ statistic
    (moving_normalized_amplitude_lower B (2 ^ k) (spectatorBulkCount k L) cg η statistic hloss hid hlower)
  have hexp : Real.exp 5 = Real.exp 3 * Real.exp 2 := by
    rw [← Real.exp_add]
    norm_num
  convert hupper using 1
  rw [hexp]
  ring

end Ostmann

end OAI
