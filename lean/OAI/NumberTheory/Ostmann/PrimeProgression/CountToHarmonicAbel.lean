import Mathlib

namespace OAI

open scoped BigOperators
open Set MeasureTheory
namespace Ostmann.Arithmetic.PrimeProgression

noncomputable def cumulativeSum (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n

lemma continuousOn_inv_sq {A B : ℝ} (hA : 0 < A) :
    ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Icc A B) := by
  apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
  intro t ht
  exact pow_ne_zero 2 (ne_of_gt (hA.trans_le ht.1))

theorem cumulativeSum_inv_sq_integrable (c : ℕ → ℝ) {A B : ℝ} (hA : 0 < A) :
    IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹ * cumulativeSum c t) (Icc A B) := by
  exact integrableOn_mul_sum_Icc c hA.le (continuousOn_inv_sq hA).integrableOn_Icc

theorem reciprocal_abel_identity (c : ℕ → ℝ) {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    (∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, (n : ℝ)⁻¹ * c n) =
      B⁻¹ * cumulativeSum c B - A⁻¹ * cumulativeSum c A +
        ∫ t in A..B, (t ^ 2)⁻¹ * cumulativeSum c t := by
  have hdiff : ∀ t ∈ Icc A B, DifferentiableAt ℝ (fun x : ℝ => x⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (ne_of_gt (hA.trans_le ht.1))).differentiableAt
  have hint : IntegrableOn (deriv (fun x : ℝ => x⁻¹)) (Icc A B) := by
    rw [deriv_inv']
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have ht0 : t ≠ 0 := ne_of_gt (hA.trans_le ht.1)
    fun_prop (disch := simp [ht0])
  have h := sum_mul_eq_sub_sub_integral_mul c hA.le hAB hdiff hint
  simp only [deriv_inv, neg_mul, integral_neg, sub_neg_eq_add] at h
  rw [intervalIntegral.integral_of_le hAB]
  exact h

end Ostmann.Arithmetic.PrimeProgression

end OAI
