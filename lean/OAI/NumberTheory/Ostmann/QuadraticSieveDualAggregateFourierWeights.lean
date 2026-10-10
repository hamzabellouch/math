import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateFourierBlocks
import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrectionRowsFourier

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate
open scoped SchwartzMap FourierTransform ArithmeticFunction.Moebius

noncomputable def dualAggregateFourierScalar (M H T : ℝ) (e d v : ℕ) : ℂ :=
  if dualWindowLower M H T e v < (d : ℝ) ∧ (d : ℝ) ≤ dualWindowUpper M H T e v
  then (μ e : ℂ)*(μ d : ℂ) else 0

theorem dualAggregateFourierScalar_norm_le (M H T : ℝ) (e d v : ℕ) :
    ‖dualAggregateFourierScalar M H T e d v‖ ≤ 1 := by
  unfold dualAggregateFourierScalar
  split_ifs
  · rw [norm_mul]
    exact (mul_le_mul (norm_moebius_complex_le_one e) (norm_moebius_complex_le_one d)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · simp

theorem dualAggregateFourierScalar_support {M H T : ℝ} {e d v : ℕ}
    (h : dualAggregateFourierScalar M H T e d v ≠ 0) :
    dualWindowLower M H T e v < (d : ℝ) := by
  unfold dualAggregateFourierScalar at h
  split_ifs at h with hc
  · exact hc.1
  · exact (h rfl).elim

theorem dualFourierDivisorRows_eq_actual_scalar (W : 𝓢(ℝ,ℂ)) (M H T : ℝ) (N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (e : ℕ) (s : ℤ) (v : ℕ) :
    dualFourierDivisorRows W M N S a e s v (dualWindowLower M H T) (dualWindowUpper M H T)
      (fun _ _ => 16*T^2) =
    (1/2 : ℂ)*∑ d ∈ Finset.Icc 1 (N^2),
      ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*dualAggregateFourierScalar M H T e d v*
        (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l d v) := by
  unfold dualFourierDivisorRows
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  change ((1/2 : ℂ)*(μ e : ℂ)*(Real.sqrt (M/((e : ℝ)*v)) : ℂ))*
      ((if dualWindowLower M H T e v < (d : ℝ) ∧ (d : ℝ) ≤ dualWindowUpper M H T e v
        then (μ d : ℂ)/(d : ℂ) else 0)*
      (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l d v)) = _
  unfold dualAggregateFourierScalar
  split_ifs with hc
  · push_cast
    ring
  · simp

end Ostmann.QuadraticSieve

end OAI
