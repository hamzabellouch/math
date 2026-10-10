import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionReindex

namespace OAI

/-! # Filtered divisor corrections retain the original coefficient arrays -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_filtered_divisor_reindex (N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (H : ℕ → ℂ) (F : ℕ → ℕ → ℂ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then F s t * (∑ d ∈ (s * t).divisors.filter P, H d) else 0) =
    ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter P,
      H d * (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        if s.Coprime t ∧ d ∣ s * t then F s t else 0) := by
  calc
    _ = ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        if s.Coprime t then
          ∑ d ∈ (s * t).divisors, if P d then H d * F s t else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      by_cases hc : s.Coprime t
      · rw [ite_eq_left hc, ite_eq_left hc, Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hp : P d <;> simp [hp, mul_comm]
      · rw [ite_eq_right hc, ite_eq_right hc]
    _ = ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
        ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
          if s.Coprime t ∧ d ∣ s * t then
            (if P d then H d * F s t else 0) else 0 :=
      quadratic_coprime_divisor_reindex N _
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hp : P d
      · simp only [hp, ite_true, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro t _
        simp only [mul_ite, mul_zero]
      · simp [hp]

theorem quadratic_low_correction_reindex (N : ℕ) (V : ℝ) (v w : ℕ → ℂ) (m : ℤ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then
        (v s * conj (w t) * quadraticGaussMultiplier (s * t) *
          (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ) / (Real.sqrt (s * t : ℕ) : ℂ)) *
        (∑ d ∈ (s * t).divisors.filter (fun d : ℕ => (d : ℝ) ≤ V),
          (ArithmeticFunction.moebius d : ℂ)) else 0) =
    ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ => (d : ℝ) ≤ V),
      (ArithmeticFunction.moebius d : ℂ) *
        quadraticGaussDivisorBilinear (2 * N) (2 * N) d
          (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) m := by
  rw [quadratic_filtered_divisor_reindex]
  apply Finset.sum_congr rfl
  intro d _
  rw [quadratic_sqrt_gauss_divisor]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  simp only [ite_mul, zero_mul, one_mul, ite_div, zero_div]

theorem quadratic_high_correction_reindex (N : ℕ) (V : ℝ) (v w : ℕ → ℂ) (m : ℤ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then
        (v s * conj (w t) * quadraticGaussMultiplier (s * t) *
          (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)) *
        (∑ d ∈ (s * t).divisors.filter (fun d : ℕ => V < (d : ℝ)),
          (ArithmeticFunction.moebius d : ℂ) / d) else 0) =
    ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ => V < (d : ℝ)),
      ((ArithmeticFunction.moebius d : ℂ) / d) *
        quadraticGaussDivisorBilinear (2 * N) (2 * N) d v w m := by
  rw [quadratic_filtered_divisor_reindex]
  apply Finset.sum_congr rfl
  intro d _
  unfold quadraticGaussDivisorBilinear
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  simp only [ite_mul, zero_mul, one_mul]

end Ostmann

end OAI
