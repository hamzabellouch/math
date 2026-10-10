import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace OAI

namespace FiniteFactor

/-- The explicit logarithm bound used in the source tag probability. -/
theorem log_one_sub_ge_neg_two {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1/2) :
    -2*t ≤ Real.log (1-t) := by
  have hp : 0 < 1-t := by linarith
  apply le_trans _ (Real.one_sub_inv_le_log_of_pos hp)
  have hh : (1-t)⁻¹ ≤ 1+2*t := by
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  linarith

/-- The source's exactly-one-tag probability has a uniform positive lower
bound, despite the growing block size. -/
theorem tag_probability_exponential_lower (m : ℕ) (hm : 100 ≤ m) :
    Real.exp (-82) ≤ (1-41/(m : ℝ))^(m-1) := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have ht0 : 0 ≤ 41/(m : ℝ) := by positivity
  have ht1 : 41/(m : ℝ) ≤ 1/2 := (div_le_iff₀ hm0).mpr (by linarith)
  have hbase : 0 < 1-41/(m : ℝ) := by linarith
  have hlog := log_one_sub_ge_neg_two ht0 ht1
  have hnum : ((m-1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (m-1) : (0 : ℝ) ≤ (m-1 : ℕ))
  have hden : (m : ℝ)*(41/(m : ℝ)) = 41 := by field_simp
  have hsmall := mul_le_mul_of_nonneg_right hnum ht0
  have hh : -82 ≤ ((m-1 : ℕ) : ℝ)*Real.log (1-41/(m : ℝ)) := by nlinarith
  have he : (1-41/(m : ℝ))^(m-1) =
      Real.exp (((m-1 : ℕ) : ℝ)*Real.log (1-41/(m : ℝ))) := by
    rw [Real.exp_nat_mul,Real.exp_log hbase]
  rw [he]
  exact Real.exp_le_exp.mpr hh

end FiniteFactor

end OAI
