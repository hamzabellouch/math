import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionReindex
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMiddleDivisor

namespace OAI

/-! # The original middle divisor correction is the bounded middle matrix -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

private theorem filtered_parameter_reindex (N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (F : ℕ → ℕ → ℕ → ℂ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then ∑ d ∈ (s * t).divisors.filter P, F s t d else 0) =
    ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter P,
      ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        if s.Coprime t ∧ d ∣ s * t then F s t d else 0 := by
  simp only [Finset.sum_filter]
  rw [quadratic_coprime_divisor_reindex]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hp : P d <;> simp [hp]

theorem quadratic_middle_correction_reindex (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M U V : ℝ) (e N b L : ℕ) (v w : ℕ → ℂ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then
        (v s * conj (w t) * quadraticGaussMultiplier (s * t) *
          (jacobiSym (b : ℤ) s : ℂ) * (jacobiSym (b : ℤ) t : ℂ)) *
        (∑ d ∈ (s * t).divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
          ((ArithmeticFunction.moebius d : ℂ) / d) *
            quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha))
              (quadraticSecondScale M e (s * t) b / d) L) else 0) =
    ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
      ((ArithmeticFunction.moebius d : ℂ) / d) *
        quadraticMiddleWindow ρ a ha M e N d v w b L := by
  simp_rw [Finset.mul_sum]
  rw [filtered_parameter_reindex]
  apply Finset.sum_congr rfl
  intro d _
  unfold quadraticMiddleWindow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [ite_mul, zero_mul, one_mul, mul_ite, mul_zero]
  split_ifs <;> ring

end Ostmann

end OAI
