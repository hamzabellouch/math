import OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPaddingLaw

namespace OAI

/-! Exact first moments of additive prime costs under the actual padding law. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma padding_selected_prime_sum (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (b : Q → Bool) (c : ℕ → ℝ) :
    (∑ p ∈ (paddingSelectedDivisor Q b).primeFactors, c p) =
      ∑ p : Q, if b p then c p.val else 0 := by
  rw [paddingSelectedDivisor_primeFactors Q hQ, paddingAvailablePrimes, sum_image]
  · simp only [selectedCoordinates, sum_filter]
  · intro p _ r _ he
    exact Subtype.ext he

lemma padding_prime_cost_average (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (c : ℕ → ℝ) :
    (reciprocalPaddingLaw Q).average
      (fun b => ∑ p ∈ (paddingSelectedDivisor Q b).primeFactors, c p) =
        ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * c p := by
  simp only [padding_selected_prime_sum Q hQ]
  rw [FiniteLaw.average_sum, ← sum_coe_sort Q]
  apply sum_congr rfl
  intro p _
  rw [reciprocalPaddingLaw, FiniteLaw.independent_average_coordinate
    (fun p : Q => reciprocalPaddingPrimeLaw p.val) p
    (fun b : Bool => if b then c p.val else 0)]
  simp [reciprocalPaddingPrimeLaw, booleanLaw, FiniteLaw.average]

lemma padding_prime_cost_sum (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (c : ℕ → ℝ) :
    (∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) *
      ∑ p ∈ q.primeFactors, c p) =
        paddingTiltNormalizer Q * ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * c p := by
  have he := reciprocal_padding_average Q hQ (fun q => ∑ p ∈ q.primeFactors, c p)
  rw [padding_prime_cost_average Q hQ] at he
  have hS := paddingTiltNormalizer_pos Q
  calc
    _ = paddingTiltNormalizer Q * ((paddingTiltNormalizer Q)⁻¹ *
        ∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) *
          ∑ p ∈ q.primeFactors, c p) := by
      rw [← mul_assoc, mul_inv_cancel₀ hS.ne', one_mul]
    _ = _ := by rw [← he]

lemma padding_reciprocal_cost_sum_le (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    (∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) *
      ∑ p ∈ q.primeFactors, 1 / (p : ℝ)) ≤
        paddingTiltNormalizer Q * (4 * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2) := by
  rw [padding_prime_cost_sum Q hQ]
  apply mul_le_mul_of_nonneg_left _ (paddingTiltNormalizer_pos Q).le
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).pos
  have he : 4 / ((p : ℝ) + 4) ≤ 4 / (p : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hpR (by linarith)
  calc
    _ ≤ (4 / (p : ℝ)) * (1 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
