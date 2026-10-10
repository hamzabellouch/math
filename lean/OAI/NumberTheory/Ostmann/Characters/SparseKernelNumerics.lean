import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # Fixed numerical margins in the local contraction -/

namespace Ostmann

/-- The scalar decrease survives both the square kernel and the cost of the
side blocks. The fixed epsilon here is deliberately smaller than necessary. -/
theorem sparse_kernel_numeric_margin (p ε s U : ℝ) (hp : 100 ≤ p)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hs : s ≤ 1 - (17 / 10) * (1 - ε ^ 2) / p + (289 / 100) * ε / p)
    (hU : 1 - 4 * ε / p ≤ U) :
    s + 20 * (6 * ε / Real.sqrt p) ^ 2 ≤ U * (1 - (8 / 5) / p) := by
  have hp0 : 0 < p := by linarith
  have hsq : ε ^ 2 ≤ ε := by nlinarith
  have hbudget : (17 / 10 + 720) * ε ^ 2 + (289 / 100) * ε ≤ (1 / 100 : ℝ) := by
    nlinarith
  have hscale : 20 * (6 * ε / Real.sqrt p) ^ 2 = 720 * ε ^ 2 / p := by
    rw [div_pow, Real.sq_sqrt hp0.le]
    ring
  have hleft : s + 720 * ε ^ 2 / p ≤ 1 - (169 / 100) / p := by
    have hm := mul_le_mul_of_nonneg_right hs hp0.le
    simp only [add_mul, sub_mul, one_mul, div_mul_cancel₀ _ hp0.ne'] at hm
    apply (mul_le_mul_iff_of_pos_right hp0).mp
    simp only [add_mul, sub_mul, one_mul, div_mul_cancel₀ _ hp0.ne']
    nlinarith
  have hf : 0 ≤ 1 - (8 / 5) / p := by
    have hh : (8 / 5 : ℝ) / p ≤ 1 := (div_le_one hp0).mpr (by linarith)
    linarith
  rw [hscale]
  apply hleft.trans
  apply le_trans _ (mul_le_mul_of_nonneg_right hU hf)
  have hsmall : 4 * ε ≤ (1 / 100 : ℝ) := by linarith
  have hmain : 1 - (169 / 100) / p ≤ 1 - ((8 / 5) + 4 * ε) / p := by
    have hn : (8 / 5) + 4 * ε ≤ (169 / 100 : ℝ) := by linarith
    exact sub_le_sub_left ((div_le_div_iff_of_pos_right hp0).mpr hn) 1
  apply hmain.trans
  have hpos : 0 ≤ (4 * ε / p) * ((8 / 5) / p) := by positivity
  calc
    _ = (1 - 4 * ε / p) * (1 - (8 / 5) / p) -
        (4 * ε / p) * ((8 / 5) / p) := by rw [add_div]; ring
    _ ≤ _ := sub_le_self _ hpos

end Ostmann

end OAI
