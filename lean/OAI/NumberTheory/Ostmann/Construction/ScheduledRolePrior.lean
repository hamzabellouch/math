import OAI.NumberTheory.Ostmann.Construction.CopiedPriorFubini
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # The same original marginal follows every surviving copy -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def scheduledRolePrior {I A : Type*} (role : I → CopyScheduleRole)
    (μ : I → A → ℝ) (n : ℕ)
    (i : {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i}) (a : A) : ℝ :=
  μ (copyScheduleOrigin n i.val) a

theorem scheduledRolePrior_nonneg {I A : Type*} (role : I → CopyScheduleRole)
    (μ : I → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (n : ℕ)
    (i : {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i}) (a : A) :
    0 ≤ scheduledRolePrior role μ n i a := hμ _ _

theorem scheduledRolePrior_mass {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (μ : I → A → ℝ) (hμ : ∀ i, ∑ a, μ i a = 1) (n : ℕ) :
    (∑ x : ({i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → A),
      ∏ i, scheduledRolePrior role μ n i (x i)) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [scheduledRolePrior, hμ, Finset.prod_const_one]

theorem scheduledRolePrior_copied {I A : Type*} (role : I → CopyScheduleRole)
    (μ : I → A → ℝ) (n : ℕ)
    (i : (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n) (a : A) :
    scheduledRolePrior role μ (n + 1) (scheduledOutputVertex role n i) a =
      match i with
      | .inl (_, h) => μ (copyScheduleOrigin n h.val) a
      | .inr y => μ (copyScheduleOrigin n y.val) a := by
  rcases i with ⟨b, h⟩ | y <;> rfl

/-- The inherited original marginals give exactly two independent H priors,
while every outside marginal is still present exactly once. -/
theorem scheduledRolePrior_copied_product {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (μ : I → A → ℝ) (n : ℕ)
    (u : CopyScheduleY role n → A) (l r : CopyScheduleH role n → A) :
    (∏ i, scheduledRolePrior role μ (n + 1) i (scheduledCopiedAssignment role n u l r i)) =
      (∏ y, μ (copyScheduleOrigin n y.val) (u y)) *
      (∏ h, μ (copyScheduleOrigin n h.val) (l h)) *
      (∏ h, μ (copyScheduleOrigin n h.val) (r h)) := by
  rw [scheduledCopiedAssignment_prior]
  simp only [scheduledRolePrior_copied]

/-- Harmonic marginal normalization holds on the actual surviving schedule,
including unequal original prime cells. -/
theorem scheduledHarmonicPrior_mass {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (P : Finset ℕ) (Q : I → Finset ℕ)
    (hQP : ∀ i, Q i ⊆ P) (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0) (n : ℕ) :
    (∑ x : ({i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → P),
      ∏ i, scheduledRolePrior role (fun j => primeSubsetPrior P (Q j)) n i (x i)) = 1 :=
  scheduledRolePrior_mass role _ (fun i => primeSubsetPrior_mass P (Q i) (hQP i) (hQ i)) n

end Ostmann

end OAI
