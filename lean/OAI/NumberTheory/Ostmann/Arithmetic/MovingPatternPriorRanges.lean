import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPriorSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSmallFrequencyUnits

namespace OAI

/-! # Actual prior support supplies the level and prime-separation hypotheses -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_internal_prior_nonzero {A B C : Type*} [Fintype B] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A)
    (hx : movingOriginalPatternWeight e μ ν prime n pattern G x ≠ 0) :
    ∀ i, μ (movingSampleTier i.2) (x (e.symm (.inr (pattern i)))) ≠ 0 := by
  have hm : movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
      (fun i => x (e.symm (.inr (pattern i))))) ≠ 0 := by
    intro hz
    apply hx
    simp only [movingOriginalPatternWeight, hz, Complex.ofReal_zero, mul_zero, zero_mul]
  have hp := movingPairCompensatedMass_pattern μ prime n pattern
    (fun c => x (e.symm (.inr c)))
  change movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
    (fun i => x (e.symm (.inr (pattern i))))) = _ at hp
  rw [hp] at hm
  intro i
  exact (mul_ne_zero_iff.mp
    (Finset.prod_ne_zero_iff.mp hm i (Finset.mem_univ _))).2

/-- Incompatible level identifications have zero original weight. This
permits retaining all setoids in the exact expansion. -/
theorem movingPattern_tier_consistent_of_nonzero {A B C : Type*} [Fintype B] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (tier : A → ℕ) (hμ : ∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A)
    (hx : movingOriginalPatternWeight e μ ν prime n pattern G x ≠ 0) :
    ∀ i, movingSampleTier (rep (pattern i)).val.2 = movingSampleTier i.2 := by
  have hp := movingPattern_internal_prior_nonzero e μ ν prime pattern G x hx
  intro i
  have hi := hμ _ (movingSampleTier_lt i.2) _ (hp i)
  have hr := hμ _ (movingSampleTier_lt (rep (pattern i)).val.2) _ (hp (rep (pattern i)).val)
  rw [(rep (pattern i)).property] at hr
  exact hr.symm.trans hi

theorem movingPattern_zero_of_inconsistent_tiers {A B C : Type*} [Fintype B] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (tier : A → ℕ) (hμ : ∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j)
    (hbad : ¬ ∀ i, movingSampleTier (rep (pattern i)).val.2 = movingSampleTier i.2)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A) :
    movingOriginalPatternWeight e μ ν prime n pattern G x = 0 := by
  by_contra hx
  exact hbad (movingPattern_tier_consistent_of_nonzero e μ ν prime pattern rep tier hμ G x hx)

theorem movingPattern_prior_tiers {A B C : Type*} {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (tier : A → ℕ) (tierB : B → ℕ)
    (hμ : ∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j)
    (hν : ∀ j a, ν j a ≠ 0 → tier a = tierB j)
    (x : Fin (N + 1) → A)
    (hx : productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :
    ∀ i, tier (x i) = (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e i) := by
  intro i
  have hi := Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ _)
  cases he : e i with
  | inl b => exact hν b (x i) (by simpa only [he, Sum.elim_inl] using hi)
  | inr c => exact hμ _ (movingSampleTier_lt (rep c).val.2) (x i) (by simpa only [he, Sum.elim_inr] using hi)

theorem movingPattern_prior_prime_separation {A B C : Type*} {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (tier : A → ℕ) (tierB : B → ℕ) (prime : A → ℕ) (hinj : Function.Injective prime)
    (hμ : ∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j)
    (hν : ∀ j a, ν j a ≠ 0 → tier a = tierB j)
    (hB : ∀ b, n ≤ tierB b) (x : Fin (N + 1) → A)
    (hx : productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :
    (∀ i j, (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e i) ≠
      (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e j) →
        prime (x i) ≠ prime (x j)) ∧
    (∀ b c, prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c)))) := by
  have ht := movingPattern_prior_tiers e μ ν pattern rep tier tierB hμ hν x hx
  have hd (i j) (hij : (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e i) ≠
      (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e j)) :
      prime (x i) ≠ prime (x j) := by
    intro hp
    apply hij
    rw [← ht i, ← ht j, hinj hp]
  refine ⟨hd, ?_⟩
  intro b c
  apply hd
  simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr]
  have hc := movingSampleTier_lt (rep c).val.2
  have hb := hB b
  omega

end Ostmann

end OAI
