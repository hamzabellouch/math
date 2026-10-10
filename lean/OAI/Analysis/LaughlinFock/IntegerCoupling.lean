import Mathlib
import OAI.Analysis.LaughlinFock.RationalCoupling

namespace OAI

/-! Integer Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Polynomial

 
def integerCoupling (c : ℤ) (z k p : ℕ) : ℤ :=
  ∑ h ∈ Finset.range (p+1), (-1)^(z-h) * (z.choose h : ℤ) *
    (k.choose (p-h) : ℤ) * c^(p-h)

theorem rationalCoupling_integer (c : ℤ) (z k p : ℕ) :
    rationalCoupling (c:ℚ) z k p = (integerCoupling c z k p : ℚ) := by
  have h1 : ((X-1)^z : Polynomial ℚ).coeff = fun h =>
      (-1)^(z-h) * (z.choose h : ℚ) := by
    funext h
    rw [show (X-1:Polynomial ℚ) = X+C (-1) by simp [sub_eq_add_neg]]
    exact coeff_X_add_C_pow (-1) z h
  have h2 : ((C (c:ℚ)*X+1)^k : Polynomial ℚ).coeff = fun h =>
      (k.choose h : ℚ) * (c:ℚ)^h := by
    funext h
    rw [show ((C (c:ℚ)*X+1)^k : Polynomial ℚ) = ((X+1)^k).comp (C (c:ℚ)*X) by simp]
    rw [comp_C_mul_X_coeff, coeff_X_add_one_pow]
  unfold rationalCoupling integerCoupling
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [h1, h2, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro h _
  ring

end LaughlinFock
end

end OAI
