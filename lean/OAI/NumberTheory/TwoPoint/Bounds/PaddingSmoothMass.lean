import OAI.NumberTheory.TwoPoint.Bounds.SmoothReciprocalMass
import OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPaddingLaw

namespace OAI

/-! Averaging smooth-dilation costs under the actual padding divisor law.
Only one factor is paid at each selected prime. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma smoothReciprocalProduct_selected (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (b : Q → Bool) (s : ℝ) :
    smoothReciprocalProduct (paddingSelectedDivisor Q b).primeFactors s =
      ∏ p : Q, if b p then (1 - (p.val : ℝ) ^ (-s))⁻¹ else 1 := by
  rw [paddingSelectedDivisor_primeFactors Q hQ, smoothReciprocalProduct,
    paddingAvailablePrimes, prod_image]
  · simp only [selectedCoordinates, prod_filter]
  · intro p _ r _ hpr
    exact Subtype.ext hpr

lemma padding_smooth_reciprocal_average (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (s : ℝ) :
    (reciprocalPaddingLaw Q).average
      (fun b => smoothReciprocalProduct (paddingSelectedDivisor Q b).primeFactors s) =
      ∏ p : Q, (1 + 4 / ((p.val : ℝ) + 4) *
        ((1 - (p.val : ℝ) ^ (-s))⁻¹ - 1)) := by
  simp only [smoothReciprocalProduct_selected Q hQ]
  rw [reciprocalPaddingLaw,
    FiniteLaw.independent_average_product (fun p : Q => reciprocalPaddingPrimeLaw p.val)
      (fun (p : Q) (b : Bool) => if b then (1 - (p.val : ℝ) ^ (-s))⁻¹ else 1)]
  apply prod_congr rfl
  intro p _
  simp only [FiniteLaw.average, reciprocalPaddingPrimeLaw, booleanLaw, Fintype.sum_bool,
    Bool.false_eq_true, ite_false, ite_true, mul_one]
  ring

lemma padding_smooth_reciprocal_sum (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (s : ℝ) :
    (∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) *
      smoothReciprocalProduct q.primeFactors s) =
      paddingTiltNormalizer Q *
        ∏ p : Q, (1 + 4 / ((p.val : ℝ) + 4) *
          ((1 - (p.val : ℝ) ^ (-s))⁻¹ - 1)) := by
  have he := reciprocal_padding_average Q hQ
    (fun q => smoothReciprocalProduct q.primeFactors s)
  rw [padding_smooth_reciprocal_average Q hQ] at he
  have hpos := paddingTiltNormalizer_pos Q
  calc
    _ = paddingTiltNormalizer Q *
        ((paddingTiltNormalizer Q)⁻¹ *
          ∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) *
            smoothReciprocalProduct q.primeFactors s) := by
      rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    _ = _ := by rw [← he]

end TwoPointCorrelations

end OAI
