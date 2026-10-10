import OAI.NumberTheory.TwoPoint.Bounds.PrimeTuplePool
import OAI.NumberTheory.TwoPoint.Bounds.PrimeDegreeTail
import OAI.NumberTheory.TwoPoint.Bounds.PaddingDivisorEncoding

namespace OAI

/-! Exact normalizers for summing the deletion estimates over the
one-prime-per-band tuple family and retained padding divisors. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma tuple_normalizer_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (∑ d ∈ primeTupleDivisors P, positivePrimeNormalizer d.primeFactors) =
      (2 : ℝ) ^ J * ∏ j, primeHarmonicMass (P j) := by
  calc
    _ = ∑ d ∈ primeTupleDivisors P, (2 : ℝ) ^ J / d := by
      apply sum_congr rfl
      intro d hd
      have ha := primeTupleDivisors_arithmetic P hprime hdisjoint hd
      rw [positivePrimeNormalizer_squarefree d ha.1, ha.2.1]
    _ = (2 : ℝ) ^ J * ∑ d ∈ primeTupleDivisors P, 1 / (d : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ = _ := by rw [primeTupleDivisors_mass P hprime hdisjoint]; simp only [primeHarmonicMass_eq_sum]

lemma retained_padding_mass_le (Q D : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hD : D ⊆ retainedPrimeDivisors Q) :
    (∑ q ∈ D, actualPaddingCoefficient q / (q : ℝ)) ≤ paddingTiltNormalizer Q := by
  rw [paddingTiltNormalizer_eq_divisor_sum Q hQ]
  apply sum_le_sum_of_subset_of_nonneg hD
  intro q _ _
  unfold actualPaddingCoefficient
  positivity

lemma tuple_normalizer_sum_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (D : Finset ℕ) (hD : D ⊆ primeTupleDivisors P) :
    (∑ d ∈ D, positivePrimeNormalizer d.primeFactors) ≤
      (2 : ℝ) ^ J * ∏ j, primeHarmonicMass (P j) := by
  rw [← tuple_normalizer_sum P hprime hdisjoint]
  exact sum_le_sum_of_subset_of_nonneg hD (fun d _ _ => by
    unfold positivePrimeNormalizer
    positivity)

lemma tuple_padding_normalizer_sum_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Q D : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hD : D ⊆ primeTupleDivisors P)
    (padding : ℕ → Finset ℕ) (hpadding : ∀ d ∈ D, padding d ⊆ retainedPrimeDivisors Q) :
    (∑ d ∈ D, positivePrimeNormalizer d.primeFactors *
      ∑ q ∈ padding d, actualPaddingCoefficient q / (q : ℝ)) ≤
        (2 : ℝ) ^ J * (∏ j, primeHarmonicMass (P j)) * paddingTiltNormalizer Q := by
  calc
    _ ≤ ∑ d ∈ D, positivePrimeNormalizer d.primeFactors * paddingTiltNormalizer Q := by
      apply sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left (retained_padding_mass_le Q (padding d) hQ (hpadding d hd))
      unfold positivePrimeNormalizer
      positivity
    _ = (∑ d ∈ D, positivePrimeNormalizer d.primeFactors) * paddingTiltNormalizer Q :=
      (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (tuple_normalizer_sum_le P hprime hdisjoint D hD)
      (paddingTiltNormalizer_pos Q).le

end TwoPointCorrelations

end OAI
