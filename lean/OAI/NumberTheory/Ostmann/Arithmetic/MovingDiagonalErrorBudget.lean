import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # The retained comparison errors in the full diagonal estimate -/

namespace Ostmann
open Filter

theorem moving_diagonal_four_term_bound (A bad D g e E : ℝ)
    (hA : 0 ≤ A) (hbad0 : 0 ≤ bad) (heD : e ≤ D) (heg : e ≤ g)
    (hbad : A * bad * D ≤ E) (hgood : A * g ≤ E) :
    A * (4 * (bad * (D + 5 * e) + g + 5 * e)) ≤ 48 * E := by
  have hb := mul_le_mul_of_nonneg_left heD (mul_nonneg hA hbad0)
  have hg := mul_le_mul_of_nonneg_left heg hA
  nlinarith only [hb, hg, hbad, hgood]

theorem eventual_moving_comparison_error (k : ℕ) (gain : ℝ) (hgain : 0 ≤ gain) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) ≤
        Real.exp (-gain * (spectatorBulkCount k L : ℝ)) := by
  filter_upwards [arithmetic_exponent_absorption 0 (12 / 10000) 0
    (gain * (k : ℝ) ^ 4) 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with L h hL
  have hm := mul_le_mul_of_nonneg_left (spectatorBulkCount_upper k L hL) hgain
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one, one_mul] at h
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (mul_nonneg hgain (pow_nonneg (Nat.cast_nonneg k) 4)) hL]

theorem moving_diagonal_reserve (B r m E : ℝ) (hrm : Real.log 48 ≤ 3 * r * m)
    (hE : E ≤ 48 * Real.exp (-(2 * B + 6) * r * m)) :
    E ≤ Real.exp (-(2 * B + 3) * r * m) := by
  apply hE.trans
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 48), ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

end Ostmann

end OAI
