import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace OAI

/-! # The two fixed product-state parameters

The manuscript uses `exp (-1)` and `exp (-sqrt 2)`. Their logarithms
generate an incommensurable pair of modular frequencies. No parameter
depends on an algebra, representation, or requested perturbation bound.
-/

namespace KadisonKastler

noncomputable section

def fixedProductLambda : ℝ := Real.exp (-1)

def fixedProductMu : ℝ := Real.exp (-Real.sqrt 2)

theorem fixedProductLambda_pos : 0 < fixedProductLambda := Real.exp_pos _

theorem fixedProductMu_pos : 0 < fixedProductMu := Real.exp_pos _

theorem fixedProductLambda_lt_one : fixedProductLambda < 1 := by
  exact Real.exp_lt_one_iff.mpr (by norm_num)

theorem fixedProductMu_lt_one : fixedProductMu < 1 := by
  apply Real.exp_lt_one_iff.mpr
  exact neg_lt_zero.mpr (Real.sqrt_pos.2 (by norm_num))

theorem fixedProduct_log_ratio_irrational :
    Irrational (Real.log fixedProductLambda / Real.log fixedProductMu) := by
  simpa only [fixedProductLambda, fixedProductMu, Real.log_exp,
    neg_div_neg_eq, one_div] using irrational_sqrt_two.inv

/-- The normalization by `2π` comes from Mathlib's Fourier convention;
it leaves the irrational frequency ratio unchanged. -/
theorem fixedProduct_frequency_ratio_irrational :
    Irrational ((Real.log fixedProductLambda / (2 * Real.pi)) /
      (Real.log fixedProductMu / (2 * Real.pi))) := by
  have hp : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hm : Real.log fixedProductMu ≠ 0 := by
    simp only [fixedProductMu, Real.log_exp, neg_ne_zero]
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have he : (Real.log fixedProductLambda / (2 * Real.pi)) /
      (Real.log fixedProductMu / (2 * Real.pi)) =
        Real.log fixedProductLambda / Real.log fixedProductMu := by
    field_simp
  rw [he]
  exact fixedProduct_log_ratio_irrational

end

end KadisonKastler

end OAI
