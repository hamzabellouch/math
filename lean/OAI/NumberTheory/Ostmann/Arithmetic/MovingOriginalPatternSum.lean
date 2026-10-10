import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternSumCoordinates

namespace OAI

/-! # Original pattern weights and their exact zero extension -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingPatternInjectionGuard {A B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (G : (Fin (N + 1) → A) → ℂ)
    (x : Fin (N + 1) → A) : ℂ :=
  if Function.Injective (fun c => x (e.symm (.inr c))) then G x else 0

theorem movingPatternInjectionGuard_norm {A B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (G : (Fin (N + 1) → A) → ℂ)
    (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D) (x : Fin (N + 1) → A) :
    ‖movingPatternInjectionGuard e G x‖ ≤ D := by
  unfold movingPatternInjectionGuard
  split_ifs
  · exact hG x
  · simpa only [norm_zero] using hD

theorem movingPatternInjectionGuard_nonzero {A B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (G : (Fin (N + 1) → A) → ℂ)
    (x : Fin (N + 1) → A) (hx : movingPatternInjectionGuard e G x ≠ 0) :
    Function.Injective (fun c => x (e.symm (.inr c))) ∧ G x ≠ 0 := by
  unfold movingPatternInjectionGuard at hx
  split_ifs at hx with h
  · exact ⟨h, hx⟩
  · exact False.elim (hx rfl)

/-- The original dependent pattern coefficient with independent external
priors is exactly the full finite-coordinate sum with this support mask. -/
theorem movingOriginalPattern_sum_fin {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (n : ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (G : (Fin (N + 1) → A) → ℂ) :
    (∑ y : B → A, ∑ z : {z : C → A // Function.Injective z},
      ((∏ b, ν b (y b) : ℝ) : ℂ) *
        (internalPatternWeight pattern (fun i => μ (movingSampleTier i.2)) prime z.val : ℂ) *
        G (fun i => Sum.elim y z.val (e i))) =
    ∑ x : Fin (N + 1) → A, ((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
      (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
        (fun i => x (e.symm (.inr (pattern i))))) : ℂ) * movingPatternInjectionGuard e G x := by
  rw [sum_external_injective_pattern_fin e (fun y z =>
    ((∏ b, ν b (y b) : ℝ) : ℂ) *
      (internalPatternWeight pattern (fun i => μ (movingSampleTier i.2)) prime z : ℂ) *
      G (fun i => Sum.elim y z (e i)))]
  apply Finset.sum_congr rfl
  intro x _
  have heval : (fun i => Sum.elim (fun b => x (e.symm (.inl b)))
      (fun c => x (e.symm (.inr c))) (e i)) = x := by
    have h (j : B ⊕ C) : Sum.elim (fun b => x (e.symm (.inl b)))
        (fun c => x (e.symm (.inr c))) j = x (e.symm j) := by cases j <;> rfl
    funext i
    rw [h, Equiv.symm_apply_apply]
  rw [heval]
  have hp := movingPairCompensatedMass_pattern μ prime n pattern
    (fun c => x (e.symm (.inr c)))
  simp only [Function.comp_def] at hp
  rw [hp]
  unfold movingPatternInjectionGuard
  split_ifs <;> simp only [mul_zero]

end Ostmann

end OAI
