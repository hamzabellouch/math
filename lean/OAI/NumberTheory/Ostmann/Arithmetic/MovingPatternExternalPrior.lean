import OAI.NumberTheory.Ostmann.Arithmetic.MovingSamplePatternBudget
import OAI.NumberTheory.Ostmann.Construction.FiniteProductPrior
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticLineIntegration

namespace OAI

/-! # Original external priors joined to the internal equality-pattern law

Only internal occurrences incur the repetition loss; the bound is uniform
in the number of external and protected bulk coordinates.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_external_prior_bound {A B C : Type*} [Fintype B] [Fintype C]
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ) (n : ℕ)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (B ⊕ C → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (x : B ⊕ C → A) :
    ‖((∏ b, ν b (x (.inl b)) : ℝ) : ℂ) *
        (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
          (fun i => x (.inr (pattern i)))) : ℂ) * G x‖ *
      (∏ c, (prime (x (.inr c)) : ℝ)⁻¹) ≤
    (D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
      ∏ i : B ⊕ C,
        (Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) i) (x i) := by
  let ext : B → A := fun b => x (.inl b)
  let inside : C → A := fun c => x (.inr c)
  have hx : Sum.elim ext inside = x := by
    funext i
    cases i <;> rfl
  have h := movingPairCompensatedMass_pattern_bound μ prime n pattern rep E hprime hμ hbound
    (fun y => G (Sum.elim ext y)) D hD (fun y => hG _) inside
  rw [hx] at h
  have he : 0 ≤ ∏ b, ν b (ext b) := Finset.prod_nonneg (fun b _ => hν b _)
  have hh := mul_le_mul_of_nonneg_left h he
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg he]
  simp only [norm_mul] at hh
  convert hh using 1 <;> dsimp only [ext, inside, Function.comp_def] <;> ring

/-- The same original-law bound in the exact finite coordinates of the
symbolic-line comparison. External coordinates do not enter the loss. -/
theorem movingPattern_fin_prior_bound {A B C : Type*} [Fintype B] [Fintype C]
    {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ) (n : ℕ)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (x : Fin (N + 1) → A) :
    ‖((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
        (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
          (fun i => x (e.symm (.inr (pattern i))))) : ℂ) * G x‖ *
      (∏ c, internalLineScalar true (prime (x (e.symm (.inr c))))) ≤
    (D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
      productPrior (fun i => Sum.elim ν
        (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x := by
  let y : B ⊕ C → A := x ∘ e.symm
  have hy : y ∘ e = x := by funext i; exact congrArg x (e.symm_apply_apply i)
  have h := movingPattern_external_prior_bound μ ν prime n pattern rep E hprime hμ hν hbound
    (fun z => G (z ∘ e)) D hD (fun z => hG _) y
  rw [hy] at h
  have hp := e.prod_comp (fun j =>
    (Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) j) (y j))
  simp only [y, Function.comp_apply, Equiv.symm_apply_apply] at hp
  dsimp only [y, Function.comp_apply] at h
  rw [← hp] at h
  simpa only [y, Function.comp_apply, internalLineScalar, ite_true, productPrior] using h

end Ostmann

end OAI
