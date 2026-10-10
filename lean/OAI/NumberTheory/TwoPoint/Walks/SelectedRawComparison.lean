import OAI.NumberTheory.TwoPoint.Bounds.ComplexPairSelection

namespace OAI

/-! The raw sum for a phase-selected pair family compares to one original
correlation, with its actual reciprocal prime cost and a finite boundary term. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def selectedRawMean (A : Finset (ℕ × ℕ)) (T : ℕ × ℕ → ℝ)
    (f g : ℕ → ℂ) (h : ℕ) : ℂ :=
  ∑ dq ∈ A, (actualPaddingCoefficient dq.2 : ℂ) *
    (positivePrefix (fun n => f ((dq.1 * dq.2) * n) *
      g ((dq.1 * dq.2) * (n + h))) (⌊T dq⌋₊ / (dq.1 * dq.2)) / (T dq : ℂ))

noncomputable def selectedRawCoefficient (A : Finset (ℕ × ℕ)) (f g : ℕ → ℂ) : ℂ :=
  ∑ dq ∈ A, (complexPairWeight dq : ℂ) * (f (dq.1 * dq.2) * g (dq.1 * dq.2))

lemma selectedRawMean_comparison {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (A : Finset (ℕ × ℕ)) (T : ℕ × ℕ → ℝ) (h : ℕ) (X η : ℝ)
    (hpos : ∀ dq ∈ A, 0 < dq.1 * dq.2) (hX : 0 < X) (hη : 0 ≤ η)
    (hlo : ∀ dq ∈ A, X * Real.exp (-η) ≤ T dq / (dq.1 * dq.2 : ℕ))
    (hhi : ∀ dq ∈ A, T dq / (dq.1 * dq.2 : ℕ) ≤ X) :
    ‖selectedRawMean A T f g h - selectedRawCoefficient A f g *
      (positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ))‖ ≤
      ∑ dq ∈ A, actualPaddingCoefficient dq.2 *
        ((1 / (dq.1 * dq.2 : ℕ)) *
          ((4 * (∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ))) + 2 * η + 1 / X) +
            4 * (dq.1 * dq.2).primeFactors.card / T dq) := by
  have he := weighted_dilated_correlation_comparison hfm hgm hf hg A
    (fun dq => actualPaddingCoefficient dq.2) (fun dq => dq.1 * dq.2)
    (fun dq => (dq.1 * dq.2).primeFactors) T h X η
    (fun dq _ => actualPaddingCoefficient_nonneg dq.2) hpos
    (fun dq _ _ hp => Nat.prime_of_mem_primeFactors hp)
    (fun dq hd p hp hdiv => Nat.mem_primeFactors.mpr ⟨hp, hdiv, (hpos dq hd).ne'⟩)
    hX hη hlo hhi
  have hC : (∑ dq ∈ A, (actualPaddingCoefficient dq.2 : ℂ) *
      ((f (dq.1 * dq.2) * g (dq.1 * dq.2)) / ((dq.1 * dq.2 : ℕ) : ℂ))) =
        selectedRawCoefficient A f g := by
    unfold selectedRawCoefficient complexPairWeight actualPaddingCoefficient
    push_cast
    apply sum_congr rfl
    intro dq _
    ring
  simpa only [selectedRawMean, hC] using he

lemma selectedRawComparison_cost_bound (A : Finset (ℕ × ℕ)) (T : ℕ × ℕ → ℝ)
    (X η : ℝ) (hX : 0 < X) (hT : ∀ dq ∈ A, X ≤ T dq) :
    (∑ dq ∈ A, actualPaddingCoefficient dq.2 *
      ((1 / (dq.1 * dq.2 : ℕ)) *
        ((4 * (∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ))) + 2 * η + 1 / X) +
          4 * (dq.1 * dq.2).primeFactors.card / T dq)) ≤
      4 * (∑ dq ∈ A, complexPairWeight dq *
        ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) +
      (2 * η + 1 / X) * (∑ dq ∈ A, complexPairWeight dq) +
      (∑ dq ∈ A, 4 * actualPaddingCoefficient dq.2 * (dq.1 * dq.2).primeFactors.card) / X := by
  have hpoint (dq : ℕ × ℕ) (hd : dq ∈ A) :
      actualPaddingCoefficient dq.2 *
        ((1 / (dq.1 * dq.2 : ℕ)) *
          ((4 * (∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ))) + 2 * η + 1 / X) +
            4 * (dq.1 * dq.2).primeFactors.card / T dq) ≤
      4 * (complexPairWeight dq * ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) +
        (2 * η + 1 / X) * complexPairWeight dq +
          (4 * actualPaddingCoefficient dq.2 * (dq.1 * dq.2).primeFactors.card) / X := by
    have hb := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤
        4 * (dq.1 * dq.2).primeFactors.card) hX (hT dq hd))
      (actualPaddingCoefficient_nonneg dq.2)
    unfold complexPairWeight actualPaddingCoefficient at *
    simp only [div_eq_mul_inv] at *
    nlinarith only [hb]
  calc
    _ ≤ ∑ dq ∈ A, (4 * (complexPairWeight dq *
        ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) +
        (2 * η + 1 / X) * complexPairWeight dq +
          (4 * actualPaddingCoefficient dq.2 * (dq.1 * dq.2).primeFactors.card) / X) :=
      sum_le_sum hpoint
    _ = _ := by rw [sum_add_distrib, sum_add_distrib, mul_sum, mul_sum, sum_div]

end TwoPointCorrelations

end OAI
