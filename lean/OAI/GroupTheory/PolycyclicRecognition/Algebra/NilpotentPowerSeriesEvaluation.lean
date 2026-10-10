import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Algebra.Rat

namespace OAI

/-! # Finite evaluation of rational power series at a nilpotent element

Evaluation takes place in the given associative algebra, which need not be
commutative. Nilpotence makes truncation invisible to polynomial evaluation.
-/

noncomputable section
namespace PolycyclicRecognition

theorem powerSeries_trunc_monomial (n k : ℕ) (q : ℚ) :
    PowerSeries.trunc n (Polynomial.monomial k q : PowerSeries ℚ) =
      if k < n then Polynomial.monomial k q else 0 := by
  by_cases hk : k < n
  · rw [ite_eq_left hk]
    ext d
    rw [PowerSeries.coeff_trunc, Polynomial.coeff_coe]
    by_cases hd : k = d
    · subst d; simp [hk]
    · simp [Polynomial.coeff_monomial, hd]
  · rw [ite_eq_right hk]
    ext d
    rw [PowerSeries.coeff_trunc, Polynomial.coeff_coe]
    by_cases hd : k = d
    · subst d; simp [hk]
    · simp [Polynomial.coeff_monomial, hd]

variable {A : Type*} [Ring A] [Algebra ℚ A] (a : A) {n : ℕ}

theorem aeval_powerSeries_trunc_coe (ha : a ^ n = 0) (p : Polynomial ℚ) :
    Polynomial.aeval a (PowerSeries.trunc n (p : PowerSeries ℚ)) =
      Polynomial.aeval a p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.coe_add, map_add] using congrArg₂ (· + ·) hp hq
  | monomial k q =>
    rw [powerSeries_trunc_monomial]
    split_ifs with hk
    · rfl
    · rw [map_zero, Polynomial.aeval_monomial,
        pow_eq_zero_of_le (Nat.le_of_not_gt hk) ha, mul_zero]

def nilpotentPowerSeriesEval (n : ℕ) (ha : a ^ (n + 1) = 0) : PowerSeries ℚ →+* A where
  toFun f := Polynomial.aeval a (PowerSeries.trunc (n + 1) f)
  map_zero' := by simp
  map_one' := by rw [PowerSeries.trunc_one, map_one]
  map_add' f g := by rw [map_add, map_add]
  map_mul' f g := by
    rw [← PowerSeries.trunc_trunc_mul_trunc]
    rw [← Polynomial.coe_mul, aeval_powerSeries_trunc_coe a ha, map_mul]

theorem nilpotentPowerSeriesEval_coe (n : ℕ) (ha : a ^ (n + 1) = 0) (p : Polynomial ℚ) :
    nilpotentPowerSeriesEval a n ha (p : PowerSeries ℚ) = Polynomial.aeval a p :=
  aeval_powerSeries_trunc_coe a ha p

end PolycyclicRecognition

end

end OAI
