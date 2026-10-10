import OAI.Probability.SLE.Angle.AnglePolynomialInner
import OAI.Probability.SLE.Angle.AngleRecurrenceRemainders

namespace OAI

/-! Exact norm recurrence and a uniform exponential lower bound. Together
with the coefficient bounds this controls the normalized spectral series. -/
noncomputable section
open Polynomial

namespace SLEExactGauge

def angleEigenSquareNorm (κ : ℝ) (n : ℕ) : ℝ :=
  anglePolynomialInner κ (angleEigenPolynomial κ n) (angleEigenPolynomial κ n)

lemma angleEigenSquareNorm_zero_pos {κ : ℝ} (hκ : 0<κ) :
    0<angleEigenSquareNorm κ 0 := by
  simpa only [angleEigenSquareNorm,angleEigenPolynomial_zero] using anglePolynomialInner_one_pos hκ

lemma angleEigenSquareNorm_shift {κ : ℝ} (hκ : 0<κ) (n : ℕ) :
    anglePolynomialInner κ (angleEigenPolynomial κ n) (X*angleEigenPolynomial κ (n+1))=
      angleEigenSquareNorm κ (n+1) := by
  have he := anglePolynomialInner_lower_degree hκ (n+1)
    (X*angleEigenPolynomial κ n-angleEigenPolynomial κ (n+1))
    (angleEigenPolynomial_leading_remainder κ n)
  rw [anglePolynomialInner_sub_right hκ] at he
  rw [← anglePolynomialInner_X,anglePolynomialInner_comm κ
    (X*angleEigenPolynomial κ n)]
  exact sub_eq_zero.mp he

lemma angleEigenSquareNorm_recurrence {κ : ℝ} (hκ : 0<κ) (n : ℕ) :
    angleEigenSquareNorm κ (n+1)=angleRecurrenceCoefficient κ n*angleEigenSquareNorm κ n := by
  have hd : (X*angleEigenPolynomial κ (n+1)-angleEigenPolynomial κ (n+2)-
      angleRecurrenceCoefficient κ n • angleEigenPolynomial κ n).degree < (n:WithBot ℕ) := by
    cases n with
    | zero => rw [angleEigenPolynomial_recurrence_zero hκ]; simp
    | succ n => exact angleEigenPolynomial_recurrence_remainder hκ n
  have he := anglePolynomialInner_lower_degree hκ n _ hd
  rw [anglePolynomialInner_sub_right hκ,anglePolynomialInner_sub_right hκ,
    anglePolynomialInner_smul_right,angleEigenSquareNorm_shift hκ] at he
  have hz := angleEigenPolynomial_orthogonal hκ n (n+2) (by omega)
  change anglePolynomialInner κ (angleEigenPolynomial κ n) (angleEigenPolynomial κ (n+2))=0 at hz
  rw [hz,sub_zero] at he
  exact sub_eq_zero.mp he

lemma angleEigenSquareNorm_lower {κ : ℝ} (hκ : 0<κ) (n : ℕ) :
    angleEigenSquareNorm κ 0*(κ/(4*(κ+4)))^n≤angleEigenSquareNorm κ n := by
  have hc : 0<κ/(4*(κ+4)) := by positivity
  have h0 := angleEigenSquareNorm_zero_pos hκ
  induction n with
  | zero => simp
  | succ n ih =>
    rw [angleEigenSquareNorm_recurrence hκ,pow_succ]
    calc
      _ = κ/(4*(κ+4))*(angleEigenSquareNorm κ 0*(κ/(4*(κ+4)))^n) := by ring
      _ ≤ angleRecurrenceCoefficient κ n*angleEigenSquareNorm κ n :=
        mul_le_mul (angleRecurrenceCoefficient_lower hκ n) ih
          (by positivity) (angleRecurrenceCoefficient_pos hκ n).le

lemma angleEigenSquareNorm_pos {κ : ℝ} (hκ : 0<κ) (n : ℕ) :
    0<angleEigenSquareNorm κ n :=
  lt_of_lt_of_le (by have := angleEigenSquareNorm_zero_pos hκ; positivity)
    (angleEigenSquareNorm_lower hκ n)

end SLEExactGauge

end

end OAI
