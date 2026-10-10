import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdRangeBridge
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFilteredCorrection

namespace OAI

/-! # The literal first-Poisson corrections are the bounded Gauss matrices -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_gauss_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (m : ℤ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) *
        (quadraticGaussMultiplier (quadraticPairKernel z.1 z.2) *
          (jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ) * F (quadraticPairKernel z.1 z.2))) =
      ∑ s ∈ oddSquarefreeRange (2 * quadraticGcdBlockSize R D),
        ∑ t ∈ oddSquarefreeRange (2 * quadraticGcdBlockSize R D),
          if s.Coprime t then
            (quadraticGcdBlockCoeff R D v s * conj (quadraticGcdBlockCoeff R D w t) *
              quadraticGaussMultiplier (s * t) * (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)) * F (s * t)
          else 0 := by
  rw [quadratic_gcd_block_reindex hD ho v w
    (fun q => quadraticGaussMultiplier q * (jacobiSym m q : ℂ) * F q)]
  rw [quadratic_coprime_kernel_sum (2 * quadraticGcdBlockSize R D)
    (quadraticGcdBlockCoeff R D v) (quadraticGcdBlockCoeff R D w)
    (fun q => quadraticGaussMultiplier q * (jacobiSym m q : ℂ) * F q)]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hc : s.Coprime t
  · rw [ite_eq_left hc, ite_eq_left hc,
      jacobiSym.mul_right' m (Finset.mem_filter.mp hs).2.2.ne_zero
        (Finset.mem_filter.mp ht).2.2.ne_zero, Int.cast_mul]
    ring
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem quadratic_gcd_low_correction_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (m : ℤ) (V : ℝ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) *
        (quadraticGaussMultiplier (quadraticPairKernel z.1 z.2) *
          (jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ) *
          ((1 / (Real.sqrt (quadraticPairKernel z.1 z.2) : ℂ)) *
            ∑ d ∈ (quadraticPairKernel z.1 z.2).divisors.filter (fun d : ℕ => (d : ℝ) ≤ V),
              (ArithmeticFunction.moebius d : ℂ)))) =
      ∑ d ∈ (Finset.Icc 1 ((2 * quadraticGcdBlockSize R D) ^ 2)).filter (fun d : ℕ => (d : ℝ) ≤ V),
        (ArithmeticFunction.moebius d : ℂ) *
          quadraticGaussDivisorBilinear (2 * quadraticGcdBlockSize R D) (2 * quadraticGcdBlockSize R D) d
            (quadraticSqrtNormalize (quadraticGcdBlockCoeff R D v))
            (quadraticSqrtNormalize (quadraticGcdBlockCoeff R D w)) m := by
  rw [quadratic_gcd_gauss_reindex hD ho v w m
    (fun q => (1 / (Real.sqrt q : ℂ)) *
      ∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V), (ArithmeticFunction.moebius d : ℂ))]
  rw [← quadratic_low_correction_reindex]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> ring

theorem quadratic_gcd_high_correction_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (m : ℤ) (V : ℝ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) *
        (quadraticGaussMultiplier (quadraticPairKernel z.1 z.2) *
          (jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ) *
          ∑ d ∈ (quadraticPairKernel z.1 z.2).divisors.filter (fun d : ℕ => V < (d : ℝ)),
            (ArithmeticFunction.moebius d : ℂ) / d)) =
      ∑ d ∈ (Finset.Icc 1 ((2 * quadraticGcdBlockSize R D) ^ 2)).filter (fun d : ℕ => V < (d : ℝ)),
        ((ArithmeticFunction.moebius d : ℂ) / d) *
          quadraticGaussDivisorBilinear (2 * quadraticGcdBlockSize R D) (2 * quadraticGcdBlockSize R D) d
            (quadraticGcdBlockCoeff R D v) (quadraticGcdBlockCoeff R D w) m := by
  rw [quadratic_gcd_gauss_reindex hD ho v w m
    (fun q => ∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)), (ArithmeticFunction.moebius d : ℂ) / d)]
  exact quadratic_high_correction_reindex _ V _ _ m

end Ostmann

end OAI
