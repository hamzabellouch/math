import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallCorrectionReindex

namespace OAI

/-! # Retaining the literal small-kernel divisor cutoffs after gcd removal -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_small_filtered_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (m : ℤ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (w z.2) *
      ((jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ) *
        ∑ d ∈ (2 * D * quadraticPairKernel z.1 z.2).divisors.filter P, f d)) =
      ∑ e ∈ (2 * D).divisors, ∑ d ∈ Finset.Icc 1 ((2 * quadraticGcdBlockSize R D) ^ 2),
        if P (e * d) then f (e * d) * quadraticDivisorBilinear
          (2 * quadraticGcdBlockSize R D) (2 * quadraticGcdBlockSize R D) d
            (quadraticGcdBlockCoeff R D v) (quadraticGcdBlockCoeff R D w) m else 0 := by
  simpa only [Finset.sum_filter, ite_mul, zero_mul] using
    quadratic_gcd_small_correction_reindex hD ho v w m (fun d => if P d then f d else 0)

end Ostmann

end OAI
