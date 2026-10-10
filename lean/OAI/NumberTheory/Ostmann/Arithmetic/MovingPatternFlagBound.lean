import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternArithmeticComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternUniformBudget

namespace OAI

/-! # The remaining symbolic factor retains the representative-prior bound -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_flagged_weight_bound {A B C : Type*} [Fintype B] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (x : Fin (N + 1) → A) :
    ‖movingOriginalPatternWeight e μ ν prime n pattern G x *
        movingPatternFlagProduct e prime n t small bulk pattern rep x‖ ≤
      (D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
        productPrior (fun i => Sum.elim ν
          (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x := by
  have h := movingPattern_fin_prior_bound e μ ν prime n pattern rep E hprime hμ hν hbound
    (movingPatternInjectionGuard e G) D hD (movingPatternInjectionGuard_norm e G D hD hG) x
  change ‖movingOriginalPatternWeight e μ ν prime n pattern G x‖ *
    (∏ c, internalLineScalar true (prime (x (e.symm (.inr c))))) ≤ _ at h
  apply le_trans _ h
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold movingPatternFlagProduct
  rw [norm_prod]
  apply Finset.prod_le_prod₀
  · intro c _
    exact norm_nonneg _
  · intro c _
    rw [Complex.norm_real, Real.norm_of_nonneg (internalLineFlagWeight_nonneg _ _ _)]
    exact internalLineFlagWeight_le_scalar _ _ _

/-- After normalization, all the symbolic internal factors cost only the
number of internal draws. There is no factor counting the external slots. -/
theorem movingPattern_flagged_mean_bound {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hmass : ∀ j, ∑ a, μ j a = 1) (hnmass : ∀ j, ∑ a, ν j a = 1)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D) :
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
        movingPatternFlagProduct e prime n t small bulk pattern rep x‖ ≤
      D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) := by
  let law := fun i : Fin (N + 1) =>
    Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
  have hlaw (i) : ∑ a, law i a = 1 := by
    dsimp only [law]
    cases e i with
    | inl b => exact hnmass b
    | inr c => exact hmass _
  calc
    _ ≤ ∑ x, (D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
        productPrior law x := norm_sum_le_of_le _ (fun x _ =>
      movingPattern_flagged_weight_bound e μ ν prime n t small bulk pattern rep E
        hprime hμ hν hbound G D hD hG x)
    _ = _ := by rw [← Finset.mul_sum, productPrior_mass law hlaw, mul_one]

end Ostmann

end OAI
