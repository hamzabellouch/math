import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdCorrectionReindex
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMiddleCorrectionReindex
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyTwist

namespace OAI

/-! # The original middle correction after gcd removal and the signed twist -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

theorem quadratic_gcd_middle_correction_reindex (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    {R D : ℕ} (hD : Squarefree D) (ho : Odd D) (M U V : ℝ) (e b L : ℕ)
    (v w : ℕ → ℂ) (u : ℤ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) *
        (quadraticGaussMultiplier (quadraticPairKernel z.1 z.2) *
          (jacobiSym (u * b) (quadraticPairKernel z.1 z.2) : ℂ) *
          ∑ d ∈ (quadraticPairKernel z.1 z.2).divisors.filter
              (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
            ((ArithmeticFunction.moebius d : ℂ) / d) *
              quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha))
                (quadraticSecondScale M e (quadraticPairKernel z.1 z.2) b / d) L)) =
      ∑ d ∈ (Finset.Icc 1 ((2 * quadraticGcdBlockSize R D) ^ 2)).filter
          (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
        ((ArithmeticFunction.moebius d : ℂ) / d) *
          quadraticMiddleWindow ρ a ha M e (quadraticGcdBlockSize R D) d
            (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v))
            (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D w)) b L := by
  have htw (f : ℕ → ℂ) (n : ℕ) :
      quadraticFrequencyTwist u 1 f n = (jacobiSym u n : ℂ) * f n := by
    unfold quadraticFrequencyTwist
    exact ite_eq_left (Nat.coprime_one_left n)
  rw [quadratic_gcd_gauss_reindex hD ho v w (u * b)
    (fun q => ∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
      ((ArithmeticFunction.moebius d : ℂ) / d) *
        quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha))
          (quadraticSecondScale M e q b / d) L)]
  rw [← quadratic_middle_correction_reindex]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  by_cases hc : s.Coprime t
  · simp only [ite_eq_left hc, htw, map_mul, map_intCast]
    rw [jacobiSym.mul_left, jacobiSym.mul_left, Int.cast_mul, Int.cast_mul]
    ring
  · rw [ite_eq_right hc, ite_eq_right hc]

end Ostmann

end OAI
