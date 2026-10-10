import OAI.NumberTheory.Ostmann.Construction.RepeatedPatternPrior
import OAI.NumberTheory.Ostmann.ZeroDensity.FinitePriorDensity

namespace OAI

/-! # Retaining the line-probability scale in an internal-prime pattern -/

namespace Ostmann
open scoped BigOperators

/-- The coefficient before the simultaneous line probabilities includes one
factor of the prime for every original compensation occurrence. -/
noncomputable def internalPatternWeight {I C A : Type*} [Fintype I]
    (pattern : I → C) (μ : I → A → ℝ) (prime : A → ℕ) (x : C → A) : ℝ :=
  ∏ i, (prime (x (pattern i)) : ℝ) * μ i (x (pattern i))

/-- Collapsing equal samples keeps the prior at one fixed representative and
charges only the repeated occurrences. The estimate also covers the larger
`1/(p-1)` line probability and hence the actual mixed `1/p` law. -/
theorem internalPatternWeight_bound {I C A : Type*} [Fintype I] [Fintype C]
    (pattern : I → C) (rep : ∀ c, {i : I // pattern i = c})
    (μ : I → A → ℝ) (prime : A → ℕ) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime)
    (hμ : ∀ i a, 0 ≤ μ i a) (hbound : ∀ i a, (prime a : ℝ) * μ i a ≤ E)
    (x : C → A) :
    internalPatternWeight pattern μ prime x * (∏ c, (prime (x c) : ℝ)⁻¹) ≤
      ((2 : ℝ) ^ Fintype.card C * E ^ (Fintype.card I - Fintype.card C)) *
        ∏ c, μ (rep c).val (x c) := by
  have hp : ∀ a, (2 : ℝ) ≤ prime a := fun a => by exact_mod_cast (hprime a).two_le
  have hi (c : C) : (prime (x c) : ℝ)⁻¹ ≤ ((prime (x c) : ℝ) - 1)⁻¹ := by
    apply inv_anti₀ (by linarith [hp (x c)])
    linarith
  have hw : 0 ≤ internalPatternWeight pattern μ prime x :=
    Finset.prod_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hμ i _))
  exact (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun c _ => inv_nonneg.mpr (Nat.cast_nonneg _)) (fun c _ => hi c)) hw).trans
      (repeated_pattern_prior_domination pattern rep μ (fun a => (prime a : ℝ)) E hp hμ hbound x)

theorem internalPatternWeight_complex_bound {I C A : Type*} [Fintype I] [Fintype C]
    (pattern : I → C) (rep : ∀ c, {i : I // pattern i = c})
    (μ : I → A → ℝ) (prime : A → ℕ) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime)
    (hμ : ∀ i a, 0 ≤ μ i a) (hbound : ∀ i a, (prime a : ℝ) * μ i a ≤ E)
    (G : (C → A) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hG : ∀ x, ‖G x‖ ≤ B)
    (x : C → A) :
    ‖(internalPatternWeight pattern μ prime x : ℂ) * G x‖ *
        (∏ c, (prime (x c) : ℝ)⁻¹) ≤
      (B * ((2 : ℝ) ^ Fintype.card C * E ^ (Fintype.card I - Fintype.card C))) *
        ∏ c, μ (rep c).val (x c) := by
  have hw : 0 ≤ internalPatternWeight pattern μ prime x :=
    Finset.prod_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hμ i _))
  have hc : 0 ≤ ∏ c, (prime (x c) : ℝ)⁻¹ :=
    Finset.prod_nonneg (fun c _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
  calc
    _ ≤ internalPatternWeight pattern μ prime x * B * (∏ c, (prime (x c) : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hG x) hw) hc
    _ = B * (internalPatternWeight pattern μ prime x * (∏ c, (prime (x c) : ℝ)⁻¹)) := by ring
    _ ≤ B * (((2 : ℝ) ^ Fintype.card C * E ^ (Fintype.card I - Fintype.card C)) *
        ∏ c, μ (rep c).val (x c)) :=
      mul_le_mul_of_nonneg_left (internalPatternWeight_bound pattern rep μ prime E hprime hμ hbound x) hB
    _ = _ := by ring

end Ostmann

end OAI
