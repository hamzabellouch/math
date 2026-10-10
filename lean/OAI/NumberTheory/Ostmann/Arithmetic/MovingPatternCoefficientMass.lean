import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternExternalPrior
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternArithmeticComparison

namespace OAI

/-! # The original pattern coefficients as a finite signed linear functional -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingOriginalPatternWeight_eq_coefficient_mul {A B C : Type*} [Fintype B] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (n : ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A) :
    movingOriginalPatternWeight e μ ν prime n pattern G x =
      movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x * G x := by
  unfold movingOriginalPatternWeight movingPatternInjectionGuard
  split_ifs <;> ring

/-- Only the internal classes cost a factor of the upper prime cutoff. This
bound is used solely for the negligible giant-comparison errors. -/
theorem movingPattern_coefficient_norm_le {A B C : Type*} [Fintype B] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (n : ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (E U : ℝ) (hE : 0 ≤ E) (_hU : 0 ≤ U)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (hsize : ∀ a, (prime a : ℝ) ≤ U) (x : Fin (N + 1) → A) :
    ‖movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x‖ ≤
      (((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) *
        productPrior (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x := by
  let w := movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x
  let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
  let R := ∏ c : C, (prime (x (e.symm (.inr c))) : ℝ)
  let κ := (2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)
  have hκ : 0 ≤ κ := by dsimp only [κ]; positivity
  have hprior : 0 ≤ productPrior law x := productPrior_nonneg law (by
    intro i a
    dsimp only [law]
    cases e i <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact hν _ a
    · exact hμ _ a) x
  have hR : 0 < R := Finset.prod_pos (fun c _ => by exact_mod_cast (hprime _).pos)
  have hRupper : R ≤ U ^ Fintype.card C := by
    calc
      R ≤ ∏ _c : C, U := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun _ _ => hsize _)
      _ = _ := by simp
  have hb := movingPattern_fin_prior_bound e μ ν prime n pattern rep E hprime hμ hν hbound
    (movingPatternInjectionGuard e (fun _ => 1)) 1 zero_le_one
    (movingPatternInjectionGuard_norm e (fun _ => 1) 1 zero_le_one (fun _ => by simp)) x
  have hscalar : (∏ c : C, internalLineScalar true (prime (x (e.symm (.inr c))))) = R⁻¹ := by
    simp only [internalLineScalar, ite_true, R, Finset.prod_inv_distrib]
  change ‖w‖ * _ ≤ 1 * κ * productPrior law x at hb
  rw [hscalar, one_mul] at hb
  have hm := mul_le_mul_of_nonneg_right hb hR.le
  rw [mul_assoc, inv_mul_cancel₀ hR.ne', mul_one] at hm
  calc
    ‖w‖ ≤ (κ * productPrior law x) * R := hm
    _ ≤ (κ * productPrior law x) * U ^ Fintype.card C :=
      mul_le_mul_of_nonneg_left hRupper (mul_nonneg hκ hprior)
    _ = _ := by ring

theorem movingPattern_coefficient_mass_le {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (n : ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (E U : ℝ) (hE : 0 ≤ E) (hU : 0 ≤ U)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hμmass : ∀ j, ∑ a, μ j a = 1) (hνmass : ∀ j, ∑ a, ν j a = 1)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E) (hsize : ∀ a, (prime a : ℝ) ≤ U) :
    (∑ x, ‖movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x‖) ≤
      (((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) := by
  let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
  have hlaw (i) : ∑ a, law i a = 1 := by
    dsimp only [law]
    cases e i with
    | inl b => exact hνmass b
    | inr c => exact hμmass _
  calc
    _ ≤ ∑ x, ((((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) *
      productPrior law x) := Finset.sum_le_sum (fun x _ =>
        movingPattern_coefficient_norm_le e μ ν prime n pattern rep E U hE hU hprime hμ hν hbound hsize x)
    _ = _ := by rw [← Finset.mul_sum, productPrior_mass law hlaw, mul_one]

/-- A uniform giant-comparison error is charged against the original
coefficient mass. The ideal signed mean stays inside its norm. -/
theorem movingPattern_comparison_norm {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (E U ε : ℝ) (hE : 0 ≤ E) (hU : 0 ≤ U) (hε : 0 ≤ ε)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hμmass : ∀ j, ∑ a, μ j a = 1) (hνmass : ∀ j, ∑ a, ν j a = 1)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E) (hsize : ∀ a, (prime a : ℝ) ≤ U)
    (actual ideal : (Fin (N + 1) → A) → ℂ)
    (hcompare : ∀ x, movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x ≠ 0 →
      ‖actual x - ideal x‖ ≤ ε) :
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern actual x‖ ≤
      (((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) * ε +
      ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern ideal x‖ := by
  let w := movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1)
  have herror : ‖∑ x, w x * (actual x - ideal x)‖ ≤
      (((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) * ε := by
    calc
      _ ≤ ∑ x, ‖w x‖ * ε := (norm_sum_le _ _).trans (Finset.sum_le_sum (fun x _ => by
        rw [norm_mul]
        by_cases hw : w x = 0
        · simp only [hw, norm_zero, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left (hcompare x hw) (norm_nonneg _)))
      _ = (∑ x, ‖w x‖) * ε := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (movingPattern_coefficient_mass_le e μ ν prime n pattern rep E U hE hU
          hprime hμ hν hμmass hνmass hbound hsize) hε
  have heq : (∑ x, w x * actual x) =
      (∑ x, w x * (actual x - ideal x)) + ∑ x, w x * ideal x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have ha : (∑ x, movingOriginalPatternWeight e μ ν prime n pattern actual x) =
      ∑ x, w x * actual x := Finset.sum_congr rfl (fun x _ =>
        movingOriginalPatternWeight_eq_coefficient_mul e μ ν prime n pattern actual x)
  have hi : (∑ x, movingOriginalPatternWeight e μ ν prime n pattern ideal x) =
      ∑ x, w x * ideal x := Finset.sum_congr rfl (fun x _ =>
        movingOriginalPatternWeight_eq_coefficient_mul e μ ν prime n pattern ideal x)
  rw [ha, hi, heq]
  exact (norm_add_le _ _).trans (add_le_add herror (le_refl _))

end Ostmann

end OAI
