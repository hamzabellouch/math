import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionReindex

namespace OAI

/-! # The first divisor correction gains its actual square-root denominator -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_sqrt_normalized_gauss_bound (M N D : ℕ) (hN : 0 < N)
    (v w : ℕ → ℂ) (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound M (2 * N / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound M (2 * N / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticGaussDivisorBilinear (2 * N) (2 * N) d
        (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) m‖) ≤
      3 * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) / N := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnorm : ∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) *
        quadraticDivisorMoment (2 * N) (quadraticSqrtNormalize v)) *
      Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) *
        quadraticDivisorMoment (2 * N) (quadraticSqrtNormalize w)) ≤ T / N := by
    intro i hi j hj hd₁ hd₂
    calc
      _ ≤ Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * (quadraticDivisorMoment (2 * N) v / N)) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * (quadraticDivisorMoment (2 * N) w / N)) := by
        apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
            (quadraticSqrtNormalize_moment N (2 * N) hN v hv) (by have := hK₁ i hi; positivity))
        · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
            (quadraticSqrtNormalize_moment N (2 * N) hN w hw) (by have := hK₂ j hj; positivity))
      _ = (Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w)) / N := by
        rw [← mul_div_assoc, ← mul_div_assoc, Real.sqrt_div' _ hNr.le, Real.sqrt_div' _ hNr.le,
          div_mul_div_comm, ← pow_two, Real.sq_sqrt hNr.le]
      _ ≤ _ := div_le_div_of_nonneg_right (hcost i hi j hj hd₁ hd₂) hNr.le
  have hh := quadratic_gauss_uniform_bound M (2 * N) (2 * N) D
    (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) K₁ K₂ (T / N)
    (div_nonneg hT hNr.le) hK₁ hK₂ h₁ h₂ hnorm
  convert hh using 1
  simp only [Nat.cast_add, Nat.cast_one]
  ring

end Ostmann

end OAI
