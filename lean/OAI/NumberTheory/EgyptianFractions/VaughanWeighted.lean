import OAI.NumberTheory.EgyptianFractions.VaughanIdentity
import OAI.NumberTheory.EgyptianFractions.VaughanHyperbola
import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.Vaughan

/-- Finite complex weighted sum of a real arithmetic function. -/
def weightedSum (s : Finset ℕ) (w : ℕ → ℂ) (f : ArithmeticFunction ℝ) : ℂ :=
  ∑ n ∈ s, (f n : ℂ) * w n

@[simp] theorem weightedSum_add (s : Finset ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) :
    weightedSum s w (f + g) = weightedSum s w f + weightedSum s w g := by
  simp [weightedSum, add_mul, Finset.sum_add_distrib]

@[simp] theorem weightedSum_sub (s : Finset ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) :
    weightedSum s w (f - g) = weightedSum s w f - weightedSum s w g := by
  simp [sub_eq_add_neg, weightedSum, add_mul, Finset.sum_add_distrib]

/-- Exact complex weighted Vaughan decomposition, using the canonical cutoff API. -/
theorem weighted_identity (s : Finset ℕ) (w : ℕ → ℂ) (U V : ℕ) :
    weightedSum s w Λ = weightedSum s w (shortPart V Λ) +
      weightedSum s w (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) -
      weightedSum s w (typeICoefficient U V * ζ) +
      weightedSum s w (typeIICoefficient U * longPart V Λ) := by
  have h := congrArg (weightedSum s w) (vonMangoldt_identity U V)
  simpa only [weightedSum_add, weightedSum_sub, typeICoefficient, typeIICoefficient] using h

/-- The Type II convolution is supported where both factors exceed the cutoffs. -/
theorem typeII_apply (U V n : ℕ) :
    (typeIICoefficient U * longPart V Λ) n =
      ∑ d ∈ n.divisorsAntidiagonal.filter (fun d => U < d.1 ∧ V < d.2),
        typeIICoefficient U d.1 * Λ d.2 := by
  rw [ArithmeticFunction.mul_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hU : U < d.1
  · by_cases hV : V < d.2 <;> simp [hU, hV]
  · simp [hU, typeIICoefficient_eq_zero U d.1 (not_lt.mp hU)]

lemma positive_interval (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- A convolution sum with its outer coefficient factored out. -/
theorem weightedSum_mul (N : ℕ) (w : ℕ → ℂ) (f g : ArithmeticFunction ℝ) :
    weightedSum (Finset.Ioc 0 N) w (f * g) =
      ∑ a ∈ Finset.Ioc 0 N, (f a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (g b : ℂ) * w (a * b) := by
  simpa only [weightedSum, positive_interval, Finset.mul_sum, Complex.ofReal_mul,
    mul_assoc] using sum_real_convolution_eq_nested N f g w

/-- A compactly supported coefficient restricts the outer interval exactly. -/
theorem weightedSum_mul_of_support (N A : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) (hf : ∀ a, A < a → f a = 0) :
    weightedSum (Finset.Ioc 0 N) w (f * g) =
      ∑ a ∈ Finset.Ioc 0 (min A N), (f a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (g b : ℂ) * w (a * b) := by
  rw [weightedSum_mul]
  symm
  apply Finset.sum_subset
  · intro a ha
    obtain ⟨ha0, haAN⟩ := Finset.mem_Ioc.mp ha
    exact Finset.mem_Ioc.mpr ⟨ha0, (le_min_iff.mp haAN).2⟩
  · intro a ha hnot
    have hA : A < a := by
      simp only [Finset.mem_Ioc] at ha hnot
      omega
    simp [hf a hA]

/-- Exact first Type I sum with its actual short cutoff. -/
theorem first_typeI_eq_sum (N U : ℕ) (w : ℕ → ℂ) :
    weightedSum (Finset.Ioc 0 N) w
        (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) =
      ∑ a ∈ Finset.Ioc 0 (min U N), ((μ a : ℝ) : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (Real.log b : ℂ) * w (a * b) := by
  rw [weightedSum_mul_of_support N U w _ _ (by
    intro a ha
    simp [not_le.mpr ha])]
  apply Finset.sum_congr rfl
  intro a ha
  have haU := (le_min_iff.mp (Finset.mem_Ioc.mp ha).2).1
  simp [haU]

/-- Exact second Type I sum, supported up to the product cutoff. -/
theorem second_typeI_eq_sum (N U V : ℕ) (w : ℕ → ℂ) :
    weightedSum (Finset.Ioc 0 N) w (typeICoefficient U V * ζ) =
      ∑ a ∈ Finset.Ioc 0 (min (U * V) N), (typeICoefficient U V a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), w (a * b) := by
  rw [weightedSum_mul_of_support N (U * V) w _ _ (typeICoefficient_eq_zero U V)]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  simp [ArithmeticFunction.zeta_apply_ne (Nat.ne_of_gt (Finset.mem_Ioc.mp hb).1)]

end Problem337.Vaughan

end

end OAI
