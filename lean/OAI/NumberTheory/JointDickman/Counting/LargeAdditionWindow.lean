import OAI.NumberTheory.JointDickman.Amplification.LargeNumericAddition

namespace OAI

/-! # A large-addition window contains many lag periods -/

namespace JointDickman
open Filter
open scoped Topology

theorem large_addition_window_lag {a : ℝ} (ha : 0 < a) :
    ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (W : ℝ), (j : ℝ) ≤ (B : ℝ)^2 →
      Real.exp ((B : ℝ)^a)/4 ≤ W → 2*(j : ℝ) ≤ W := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2/a) 1 (by norm_num : (0 : ℝ) < 1)).comp
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
  have ht' : Tendsto (fun B : ℕ => 8*(B : ℝ)^2*Real.exp (-((B : ℝ)^a))) atTop (𝓝 0) := by
    have hh := ht.const_mul 8
    norm_num only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with B hB
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    dsimp
    rw [← Real.rpow_mul hB0.le,show a*(2/a) = 2 by field_simp]
    simp only [Real.rpow_two,neg_one_mul]
    ring
  filter_upwards [ht'.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with B hsmall
  intro j W hj hW
  have hh : 8*(B : ℝ)^2 ≤ Real.exp ((B : ℝ)^a) := by
    rw [Real.exp_neg,← div_eq_mul_inv] at hsmall
    exact (div_le_one (Real.exp_pos _)).mp hsmall
  linarith

end JointDickman

end OAI
