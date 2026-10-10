import Mathlib
import OAI.Analysis.LaughlinFock.FastCoupling

namespace OAI

/-! Fast Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourCommonDenominator : ℕ := 2^53 * (23).factorial * 10^18

def scaledFourFactor (D : ℕ) (t : Fin 8) (b c : RowEntry t.val) : ℕ :=
  2 * 2^(53+rowP b+rowP c-(t.val+2*rowFourLevel b c)) *
    t.val.factorial * (rowI b).factorial * (rowI c).factorial *
      ((23).factorial / (rowFourLevel b c-D).factorial)

theorem scaledFourFactor_spec (D : ℕ) (t : Fin 8) (b c : RowEntry t.val) :
    (scaledFourFactor D t b c : ℚ) / (2^53 * (23).factorial) = rationalFourFactor D b c := by
  have hT := rowFourLevel_le b c
  have ht := t.isLt
  have hdvd : (rowFourLevel b c-D).factorial ∣ (23).factorial :=
    Nat.factorial_dvd_factorial (by omega)
  have hpow : (2:ℚ)^(53+rowP b+rowP c-(t.val+2*rowFourLevel b c)) *
      2^(t.val+2*rowFourLevel b c) = 2^(53+rowP b+rowP c) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  unfold scaledFourFactor rationalFourFactor
  push_cast
  rw [Nat.cast_div hdvd (by positivity : ((rowFourLevel b c-D).factorial : ℚ) ≠ 0)]
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  have hfac : ((rowFourLevel b c-D).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  simp only [← pow_mul, ← pow_add] at *
  ring_nf at *
  exact hpow

def scaledFourTrace (D : ℕ) (t : Fin 8) (r s : CopyLabel D) : ℤ :=
  -(∑ b : RowEntry t.val, ∑ c : RowEntry t.val, if D ≤ rowFourLevel b c then
    certificateAlphaData t b.val.1 b.val.2 * certificateAlphaData t c.val.1 c.val.2 *
      (scaledFourFactor D t b c : ℤ) *
      fastIntegerCopyPolynomial D (rowFourLevel b c) r.val.val (rowP b) (rowJ b) (rowI c) *
      fastIntegerCopyPolynomial D (rowFourLevel b c) s.val.val (rowP c) (rowJ c) (rowI b)
    else 0)

theorem integerFourTrace_scaled (D : ℕ) (t : Fin 8) (r s : CopyLabel D) :
    integerFourTrace D t.val (certificateAlpha t) r s =
      (scaledFourTrace D t r s : ℚ) / fourCommonDenominator := by
  unfold integerFourTrace scaledFourTrace
  simp only [integerCopyPolynomial_fast]
  simp only [Int.cast_neg, Int.cast_sum, neg_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with hh
  · simp only [Int.cast_mul, Int.cast_natCast]
    rw [← scaledFourFactor_spec D t b c]
    unfold certificateAlpha fourCommonDenominator
    push_cast
    ring
  · simp

def scaledRowsFourTrace (D : ℕ) (r s : CopyLabel D) : ℤ :=
  ∑ t : Fin 8, scaledFourTrace D t r s

theorem integerRowsFourTrace_scaled (D : ℕ) (r s : CopyLabel D) :
    integerRowsFourTrace D r s = (scaledRowsFourTrace D r s : ℚ) / fourCommonDenominator := by
  simp only [integerRowsFourTrace, Matrix.sum_apply, integerFourTrace_scaled,
    scaledRowsFourTrace, Int.cast_sum, Finset.sum_div]

end LaughlinFock
end

end OAI
