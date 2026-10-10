import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallFilteredReindex
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallMomentMain
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFullSmallHighGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFullSmallMiddleGrowth

namespace OAI

/-! # The literal small-kernel correction is the two bounded full sums -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

theorem quadratic_gcd_small_frequency_split {M : ℝ} (hM : 0 < M) (J : ℝ)
    {R D b : ℕ} (hD : Squarefree D) (ho : Odd D) (v w : ℕ → ℂ) :
    let N := quadraticGcdBlockSize R D
    let v' := quadraticGcdBlockCoeff R D v
    let w' := quadraticGcdBlockCoeff R D w
    (∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (w z.2) *
      ((jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
        quadraticSmallPairCorrection M J (2 * (quadraticPairKernel z.1 z.2 * D)) b)) =
    ∑ e ∈ (2 * D).divisors,
      (-(∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) * (Real.sqrt M : ℂ) *
        ((1 / (Real.sqrt b : ℂ)) *
          ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
            if quadraticSecondUpper (quadraticSmallScale M b) J < (e * d : ℕ) then
              ((ArithmeticFunction.moebius (e * d) : ℂ) / (e * d : ℕ)) *
                quadraticDivisorBilinear (2 * N) (2 * N) d v' w' b else 0) +
      ((Real.sqrt M : ℂ) / 2) * ((1 / (Real.sqrt b : ℂ)) *
        ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
          if quadraticSecondLower (quadraticSmallScale M b) J < (e * d : ℕ) ∧
              (e * d : ℕ) ≤ quadraticSecondUpper (quadraticSmallScale M b) J then
            (((ArithmeticFunction.moebius (e * d) : ℂ) / (e * d : ℕ)) *
              quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest quadraticSieveWeight))
                (quadraticSmallScale M b / (e * d : ℕ)) (quadraticSecondWindow J)) *
              quadraticDivisorBilinear (2 * N) (2 * N) d v' w' b else 0)) := by
  classical
  dsimp only
  let X := quadraticSmallScale M b
  let U := quadraticSecondLower X J
  let V := quadraticSecondUpper X J
  let I := ∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)
  let f := fun d : ℕ => (ArithmeticFunction.moebius d : ℂ) / d
  let g := fun d : ℕ => f d *
    quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest quadraticSieveWeight))
      (X / d) (quadraticSecondWindow J)
  have he (q : ℕ) : 2 * (q * D) = 2 * D * q := by ring
  have hsplit : (∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (w z.2) *
      ((jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
        quadraticSmallPairCorrection M J (2 * (quadraticPairKernel z.1 z.2 * D)) b)) =
      (-(X : ℂ) * I) * (∑ z ∈ quadraticGcdPairs (2 * R) D,
        v z.1 * conj (w z.2) * ((jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
          ∑ d ∈ (2 * D * quadraticPairKernel z.1 z.2).divisors.filter (fun d : ℕ => V < d), f d)) +
      ((X : ℂ) / 2) * (∑ z ∈ quadraticGcdPairs (2 * R) D,
        v z.1 * conj (w z.2) * ((jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
          ∑ d ∈ (2 * D * quadraticPairKernel z.1 z.2).divisors.filter
            (fun d : ℕ => U < d ∧ (d : ℝ) ≤ V), g d)) := by
    conv_rhs => lhs; rw [Finset.mul_sum]
    conv_rhs => rhs; rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    simp only [quadraticSmallPairCorrection, he]
    change _ = (-(X : ℂ) * I) * _ + ((X : ℂ) / 2) * _
    dsimp only [f, g, X, U, V, I]
    ring
  have hlo := quadratic_gcd_small_filtered_reindex (R := R) hD ho v w b
    (fun d => V < (d : ℝ)) f
  have hmi := quadratic_gcd_small_filtered_reindex (R := R) hD ho v w b
    (fun d => U < (d : ℝ) ∧ (d : ℝ) ≤ V) g
  simp only [Finset.sum_filter] at hlo hmi
  rw [hsplit]
  simp only [Finset.sum_filter]
  conv_lhs => lhs; arg 2; rw [hlo]
  conv_lhs => rhs; arg 2; rw [hmi]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hX : (X : ℂ) = (Real.sqrt M : ℂ) / (Real.sqrt b : ℂ) := by
    dsimp [X, quadraticSmallScale]
    rw [Real.sqrt_div hM.le, Complex.ofReal_div]
  rw [hX]
  dsimp only [f, g, U, V, X, I]
  ring_nf

end Ostmann

end OAI
