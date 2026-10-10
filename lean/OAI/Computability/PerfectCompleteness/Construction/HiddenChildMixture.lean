import OAI.Computability.PerfectCompleteness.Foundations.FiniteProduct
import OAI.Computability.PerfectCompleteness.Sampling.DensityVariation

namespace OAI

section

namespace PerfectCompleteness.HiddenChildMixture

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness SmallBias DensityVariation

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def averageDensity (q : (i : I) → Ω i → ℝ) (x : (i : I) → Ω i) : ℝ :=
  (∑ i, q i (x i)) / Fintype.card I

theorem averageDensity_mean (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (mean : ∀ i, (P i).expectation (q i) = 1) :
    (FiniteProduct.law P).expectation (averageDensity q) = 1 := by
  change (FiniteProduct.law P).expectation
    (fun x => (∑ i, q i (x i)) / Fintype.card I) = 1
  rw [expectation_div, expectation_sum]
  simp only [FiniteProduct.expectation_eval, mean, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero (α := I))

def mixture (R : I → FiniteDistribution ((i : I) → Ω i)) :
    FiniteDistribution ((i : I) → Ω i) where
  weight x := (∑ i, (R i).weight x) / Fintype.card I
  nonnegative x := div_nonneg (Finset.sum_nonneg fun i _ => (R i).nonnegative x)
    (Nat.cast_nonneg _)
  normalized := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [FiniteDistribution.normalized, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := I))

theorem mixture_density (P : (i : I) → FiniteDistribution (Ω i))
    (R : I → FiniteDistribution ((i : I) → Ω i))
    (q : (i : I) → Ω i → ℝ)
    (weight : ∀ i x, (R i).weight x = (FiniteProduct.law P).weight x * q i (x i))
    (x : (i : I) → Ω i) :
    (mixture R).weight x = (FiniteProduct.law P).weight x * averageDensity q x := by
  simp only [mixture, weight, ← Finset.mul_sum, averageDensity, mul_div_assoc]

omit [Nonempty I] in
theorem centered_cross (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (mean : ∀ i, (P i).expectation (q i) = 1)
    (i j : I) (different : i ≠ j) :
    (FiniteProduct.law P).expectation (fun x => (q i (x i) - 1) * (q j (x j) - 1)) = 0 := by
  rw [FiniteProduct.expectation_eval_mul P i j different (fun a => q i a - 1)
    (fun a => q j a - 1)]
  simp only [expectation_sub, expectation_const, mean, sub_self, mul_zero]

omit [Nonempty I] in
theorem centered_sum_second_moment (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (mean : ∀ i, (P i).expectation (q i) = 1) :
    (FiniteProduct.law P).expectation (fun x => (∑ i, (q i (x i) - 1)) ^ 2) =
      ∑ i, (P i).expectation (fun a => (q i a - 1) ^ 2) := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact FiniteProduct.expectation_eval P i (fun a => (q i a - 1) * (q i a - 1))
  · intro j _ different
    exact centered_cross P q mean j i different
  · simp

omit [DecidableEq I] [∀ i, Fintype (Ω i)] in
theorem average_centered (q : (i : I) → Ω i → ℝ) (x : (i : I) → Ω i) :
    averageDensity q x - 1 = (∑ i, (q i (x i) - 1)) / Fintype.card I := by
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := I)
  simp only [averageDensity, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp

theorem average_second_moment (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (mean : ∀ i, (P i).expectation (q i) = 1) :
    (FiniteProduct.law P).expectation (fun x => (averageDensity q x - 1) ^ 2) =
      (∑ i, (P i).expectation (fun a => (q i a - 1) ^ 2)) / (Fintype.card I : ℝ) ^ 2 := by
  simp only [average_centered, div_pow, expectation_div, centered_sum_second_moment P q mean]

theorem average_second_moment_le (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (mean : ∀ i, (P i).expectation (q i) = 1)
    (v : ℝ) (bound : ∀ i, (P i).expectation (fun a => (q i a - 1) ^ 2) ≤ v) :
    (FiniteProduct.law P).expectation (fun x => (averageDensity q x - 1) ^ 2) ≤
      v / Fintype.card I := by
  rw [average_second_moment P q mean]
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := I)
  calc
    _ ≤ (∑ _i : I, v) / (Fintype.card I : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => bound i) (sq_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

theorem observed_mixture_variation {Γ : Type*} [Fintype Γ]
    (P : (i : I) → FiniteDistribution (Ω i))
    (R : I → FiniteDistribution ((i : I) → Ω i)) (q : (i : I) → Ω i → ℝ)
    (weight : ∀ i x, (R i).weight x = (FiniteProduct.law P).weight x * q i (x i))
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (v : ℝ) (bound : ∀ i, (P i).expectation (fun a => (q i a - 1) ^ 2) ≤ v)
    (observe : ((i : I) → Ω i) → Γ) :
    ((mixture R).pushforward observe).totalVariation
        ((FiniteProduct.law P).pushforward observe) ≤ Real.sqrt (v / Fintype.card I) / 2 :=
  observed_variation_le_sqrt (FiniteProduct.law P) (mixture R) (averageDensity q)
    (mixture_density P R q weight) _ (average_second_moment_le P q mean v bound) observe

end
end PerfectCompleteness.HiddenChildMixture

end

end OAI
