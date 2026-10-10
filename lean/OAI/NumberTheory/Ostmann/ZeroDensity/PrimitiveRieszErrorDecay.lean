import OAI.NumberTheory.Ostmann.ZeroDensity.PrimitiveRieszComparison

namespace OAI

/-! # The primitive-reduction error is smaller than the Riesz contour error -/

namespace Ostmann

open Filter

theorem primitive_riesz_error_decay_log (d : ℝ) (hd : 0 < d) :
    ∀ᶠ y : ℝ in atTop, ∀ q : ℕ, (q : ℝ) ≤ Real.exp y →
      2 * q * Real.log (Real.exp (y ^ 2)) +
          4 * Real.sqrt (Real.exp (y ^ 2)) * Real.log (Real.exp (y ^ 2)) ≤
        Real.exp (y ^ 2) * Real.exp (-d * y) := by
  filter_upwards [riesz_polynomial_absorption 6 1 (by norm_num),
    eventually_ge_atTop (2 * (d + 1)), eventually_ge_atTop (2 : ℝ)] with y hp hy hy2
  intro q hq
  simp only [one_mul] at hp
  have he : (q : ℝ) ≤ Real.exp (y ^ 2 / 2) := hq.trans
    (Real.exp_le_exp.mpr (by nlinarith))
  have hp' : 6 * y ^ 2 ≤ Real.exp y := by linarith
  have hmul := mul_le_mul_of_nonneg_left hp' (Real.exp_nonneg (y ^ 2 / 2))
  have hqmul := mul_le_mul_of_nonneg_right he (sq_nonneg y)
  rw [Real.log_exp, ← Real.exp_half]
  calc
    _ ≤ Real.exp (y ^ 2 / 2) * (6 * y ^ 2) := by nlinarith
    _ ≤ Real.exp (y ^ 2 / 2) * Real.exp y := hmul
    _ = Real.exp (y ^ 2 / 2 + y) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (y ^ 2 - d * y) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by simp only [Real.exp_sub, neg_mul, Real.exp_neg, div_eq_mul_inv]

theorem primitive_riesz_error_decay (d : ℝ) (hd : 0 < d) :
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X)) →
      2 * q * Real.log X + 4 * Real.sqrt X * Real.log X ≤
        X * Real.exp (-d * Real.sqrt (Real.log X)) := by
  have ht := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (primitive_riesz_error_decay_log d hd),
    eventually_ge_atTop (1 : ℝ)] with X hX hX1
  intro q hq
  have hx : 0 < X := by linarith
  have heq : Real.exp ((Real.sqrt (Real.log X)) ^ 2) = X := by
    rw [Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log hx]
  have hh := hX q hq
  dsimp only [Function.comp_apply] at hh
  simpa only [heq] using hh

end Ostmann

end OAI
