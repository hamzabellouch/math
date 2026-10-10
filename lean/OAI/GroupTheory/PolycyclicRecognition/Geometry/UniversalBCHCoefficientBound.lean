import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialProductCoefficients
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteLogCoefficientBound
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniversalLogarithmWordCoefficients

namespace OAI

/-! # The uniform bound on the universal finite BCH coefficients -/

noncomputable section
namespace PolycyclicRecognition

theorem rationalExponentialProduct_sub_one_empty (c n : ℕ) :
    (rationalExponentialProduct c n - 1).coeff 1 = 0 := by
  simp [rationalExponentialProduct_empty_coeff, MonoidAlgebra.one_def]

theorem rationalExponentialProduct_sub_one_bound (c n : ℕ) (w : FreeMonoid (Fin n)) :
    |(rationalExponentialProduct c n - 1).coeff w| ≤ 1 := by
  by_cases hw : w = 1
  · subst w
    rw [rationalExponentialProduct_sub_one_empty, abs_zero]
    exact zero_le_one
  · simpa [MonoidAlgebra.one_def, hw, Ne.symm hw] using
      rationalExponentialProduct_coefficient_bound c n w

theorem universalLogarithmCoefficient_bound (c n : ℕ) (d : Fin c)
    (w : FreeMonoid (Fin n)) :
    |(universalLogarithmCoefficient c n (d.val + 1)).coeff w| ≤ (2 : ℚ) ^ c := by
  rw [universalLogarithmCoefficient_coeff (Nat.succ_le_of_lt d.isLt)]
  by_cases hw : w.length = d.val + 1
  · rw [ite_eq_left hw, rationalUniversalLogarithm]
    exact finiteLog_coefficient_bound _ c (rationalExponentialProduct_sub_one_empty c n)
      (rationalExponentialProduct_sub_one_bound c n) w (by omega) (by omega)
  · rw [ite_eq_right hw, abs_zero]
    positivity

theorem universalBCHCoefficient_bound (c n : ℕ) (d : Fin c)
    (w : Fin (d.val + 1) → Fin n) :
    |(d.val + 1 : ℚ)⁻¹ *
      (universalLogarithmCoefficient c n (d.val + 1)).coeff (wordOfFn w)| ≤ (2 : ℚ) ^ c := by
  rw [abs_mul, abs_inv, abs_of_nonneg (by positivity : (0 : ℚ) ≤ d.val + 1)]
  exact (mul_le_mul (inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg _)))
    (universalLogarithmCoefficient_bound c n d (wordOfFn w))
    (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

end PolycyclicRecognition

end

end OAI
