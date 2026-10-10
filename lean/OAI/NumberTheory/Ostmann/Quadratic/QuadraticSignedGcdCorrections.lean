import OAI.NumberTheory.Ostmann.Quadratic.QuadraticBilinearTwist
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdCorrectionReindex
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdMiddleCorrection

namespace OAI

/-! # Signed first-transform corrections use the original gcd coefficient arrays -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_low_signed_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (u : ℤ) (b : ℕ) (V : ℝ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) *
        (quadraticGaussMultiplier (quadraticPairKernel z.1 z.2) *
          (jacobiSym (u * b) (quadraticPairKernel z.1 z.2) : ℂ) *
          ((1 / (Real.sqrt (quadraticPairKernel z.1 z.2) : ℂ)) *
            ∑ d ∈ (quadraticPairKernel z.1 z.2).divisors.filter (fun d : ℕ => (d : ℝ) ≤ V),
              (ArithmeticFunction.moebius d : ℂ)))) =
      ∑ d ∈ (Finset.Icc 1 ((2 * quadraticGcdBlockSize R D) ^ 2)).filter (fun d : ℕ => (d : ℝ) ≤ V),
        (ArithmeticFunction.moebius d : ℂ) *
          quadraticGaussDivisorBilinear (2 * quadraticGcdBlockSize R D) (2 * quadraticGcdBlockSize R D) d
            (quadraticSqrtNormalize (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)))
            (quadraticSqrtNormalize (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D w))) b := by
  rw [quadratic_gcd_low_correction_reindex hD ho v w (u * b) V]
  apply Finset.sum_congr rfl
  intro d _
  rw [quadratic_gauss_bilinear_twist, quadratic_sqrt_twist_commute, quadratic_sqrt_twist_commute]

theorem quadratic_gcd_high_signed_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (u : ℤ) (b : ℕ) (V : ℝ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) *
        (quadraticGaussMultiplier (quadraticPairKernel z.1 z.2) *
          (jacobiSym (u * b) (quadraticPairKernel z.1 z.2) : ℂ) *
          ∑ d ∈ (quadraticPairKernel z.1 z.2).divisors.filter (fun d : ℕ => V < (d : ℝ)),
            (ArithmeticFunction.moebius d : ℂ) / d)) =
      ∑ d ∈ (Finset.Icc 1 ((2 * quadraticGcdBlockSize R D) ^ 2)).filter (fun d : ℕ => V < (d : ℝ)),
        ((ArithmeticFunction.moebius d : ℂ) / d) *
          quadraticGaussDivisorBilinear (2 * quadraticGcdBlockSize R D) (2 * quadraticGcdBlockSize R D) d
            (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v))
            (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D w)) b := by
  rw [quadratic_gcd_high_correction_reindex hD ho v w (u * b) V]
  apply Finset.sum_congr rfl
  intro d _
  rw [quadratic_gauss_bilinear_twist]

end Ostmann

end OAI
