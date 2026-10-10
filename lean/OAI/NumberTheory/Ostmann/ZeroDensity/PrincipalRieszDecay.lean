import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalRieszSupply
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszExponentialParameters

namespace OAI

/-! # Exponential decay of the principal Riesz error -/

namespace Ostmann

open Filter

theorem principal_riesz_height_log_bound (y : ℝ) (hy : 5 ≤ y) :
    0 < Real.log (Real.exp y + 4) + 1 ∧ Real.log (Real.exp y + 4) + 1 ≤ 3 * y := by
  have he : 4 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hlog : 0 ≤ Real.log (Real.exp y + 4) := Real.log_nonneg (by linarith)
  refine ⟨by linarith, ?_⟩
  have hh : Real.log (Real.exp y + 4) ≤ Real.log 2 + y := by
    calc
      _ ≤ Real.log (2 * Real.exp y) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp]
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem principal_riesz_decay : ∃ d : ℝ, 0 < d ∧ ∀ᶠ y : ℝ in atTop,
    ‖principalRieszMean (Real.exp (y ^ 2)) - (Real.exp (y ^ 2) / 2 : ℝ)‖ ≤
      3 * Real.exp (y ^ 2 - d * y) := by
  obtain ⟨c, A, B, E, hc, hc4, hA, hB, hE, hbound⟩ := principal_riesz_general_bound
  refine ⟨c / 6, by positivity, ?_⟩
  filter_upwards [riesz_exponential_error c A B E hc hc4 hA.le hB.le hE.le,
    eventually_ge_atTop (5 : ℝ)] with y hy hy5
  have hy0 : 0 < y := by linarith
  have hT : 2 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hb1 : 1 < 1 + 1 / y ^ 2 := by
    have hh : 0 < 1 / y ^ 2 := by positivity
    linarith
  have hb2 : 1 + 1 / y ^ 2 ≤ 2 := by
    have hys : 1 ≤ y ^ 2 := by nlinarith
    have hh : 1 / y ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hys
    linarith
  have hh := hbound (Real.exp y) (Real.exp (y ^ 2)) (1 + 1 / y ^ 2) hT
    (Real.one_le_exp (sq_nonneg y)) hb1 hb2
  obtain ⟨hH, hHy⟩ := principal_riesz_height_log_bound y hy5
  exact hh.trans (hy _ hH hHy)

theorem principal_riesz_sqrt_decay : ∃ d : ℝ, 0 < d ∧ ∀ᶠ X : ℝ in atTop,
    ‖principalRieszMean X - (X / 2 : ℝ)‖ ≤
      3 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
  obtain ⟨d, hd, h⟩ := principal_riesz_decay
  refine ⟨d, hd, ?_⟩
  have ht := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually h, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  have hx : 0 < X := by linarith
  have heq : Real.exp ((Real.sqrt (Real.log X)) ^ 2) = X := by
    rw [Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log hx]
  dsimp only [Function.comp_apply] at hX
  rw [heq, Real.exp_sub, Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log hx] at hX
  simpa only [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, neg_mul] using hX

end Ostmann

end OAI
