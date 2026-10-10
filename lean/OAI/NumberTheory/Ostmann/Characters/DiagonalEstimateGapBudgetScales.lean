import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateGapBudgetBasic
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceGaps

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Filter InitialCharacterScale

theorem eventually_good_diagonal_quarter (B β C BD O : ℝ) (k : ℕ)
    (hBD : diagonalGapThreshold B β C ≤ BD) :
    ∀ᶠ L : ℝ in atTop, ∀j : ℕ, ∀d : ℝ, d ≤ (wordSize k L : ℝ) →
      Real.exp (-gapSchedule BD k L (j+1)+
        (2 : ℝ)^j*(wordSize k L : ℝ)*(Real.log (depthScale k)+C+Real.log 2)+
        (β+1)*(2 : ℝ)^j*L+(wordSize k L : ℝ)+O) ≤
      (1/4 : ℝ)*Real.exp (-d)*Real.exp (-2*B*(2 : ℝ)^j*(wordSize k L : ℝ)) := by
  filter_upwards [(wordSize_tendsto k).eventually_ge_atTop (O+Real.log 4),
    eventually_ge_atTop (2 : ℝ)] with L hO hL
  intro j d hd
  have hL0 : 0 ≤ L := by linarith
  have hLm : L ≤ 2*(wordSize k L : ℝ) := by
    have hzL := mul_le_mul_of_nonneg_right (one_le_depthScale k) hL0
    have hf := (wordSize_bounds k hL0).1
    nlinarith
  have he := diagonal_good_exponent B β C BD ((2 : ℝ)^j)
    (wordSize k L) L (depthScale k) O d hBD
    (one_le_pow₀ (by norm_num)) (by positivity) hL0 hLm
    (Real.log_nonneg (one_le_depthScale k)) hO hd
  rw [←exp_quarter_target]
  apply Real.exp_le_exp.mpr
  have hs : 0 ≤ (4 : ℝ)^(j+1)*Real.sqrt (wordSize k L : ℝ) := by positivity
  dsimp only [gapSchedule,initialGap]
  nlinarith

theorem eventually_error_diagonal_quarter (B K : ℝ) (k : ℕ) {c α : ℝ}
    (hc : 0 < c) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop, ∀j : ℕ, j ≤ k → ∀d : ℝ, d ≤ (wordSize k L : ℝ) →
      Real.exp (K*L^2-c*Real.exp (α*L)) ≤
      (1/4 : ℝ)*Real.exp (-d)*Real.exp (-2*B*(2 : ℝ)^j*(wordSize k L : ℝ)) := by
  filter_upwards [eventually_quadratic_prime_exponent K
    ((1+2*|B| *(2 : ℝ)^k)*depthScale k) (Real.log 4) hc hα,
    eventually_ge_atTop (0 : ℝ)] with L he hL
  intro j hj d hd
  have hm := (wordSize_bounds k hL).2
  have hm0 : 0 ≤ (wordSize k L : ℝ) := by positivity
  have hr : (2 : ℝ)^j ≤ (2 : ℝ)^k := pow_le_pow_right₀ (by norm_num) hj
  have hb := mul_le_mul_of_nonneg_right (le_abs_self B)
    (show 0 ≤ (2 : ℝ)^j*(wordSize k L : ℝ) by positivity)
  have hr' := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ |B| *(wordSize k L : ℝ) by positivity)
  have hmass := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ 1+2*|B| *(2 : ℝ)^k by positivity)
  have htarget : d+2*B*(2 : ℝ)^j*(wordSize k L : ℝ) ≤
      ((1+2*|B| *(2 : ℝ)^k)*depthScale k)*L := by nlinarith
  rw [←exp_quarter_target]
  exact Real.exp_le_exp.mpr (by linarith)

end Ostmann.Characters.DiagonalEstimate

end

end OAI
