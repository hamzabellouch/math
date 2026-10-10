import OAI.NumberTheory.Ostmann.Arithmetic.BulkDistinctnessRemoval
import OAI.NumberTheory.Ostmann.Construction.FiniteFormulaRenaming

namespace OAI

/-! # Bulk collision removal on the original tree-and-word positions -/

namespace Ostmann
open scoped Classical BigOperators

theorem bulk_distinctness_removal_indexed {J A : Type*} [Fintype J] [Fintype A]
    (μ : J → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1) (α : ℝ) (hα : 0 ≤ α)
    (hmax : ∀ i a, μ i a ≤ α) (F : (J → A) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ x : J → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * (if Function.Injective x then F x else 0)) -
      ∑ x : J → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x‖ ≤ B * (Fintype.card J : ℝ) ^ 2 * α := by
  let e := (Fintype.equivFin J).symm
  have hi (x : Fin (Fintype.card J) → A) :
      Function.Injective (x ∘ e.symm) ↔ Function.Injective x := by
    constructor
    · intro h
      simpa only [Function.comp_def, Equiv.symm_apply_apply] using h.comp e.injective
    · intro h
      exact h.comp e.symm.injective
  have he₁ := finite_prior_reindex e μ (fun x => if Function.Injective x then F x else 0)
  simp_rw [hi] at he₁
  have he₂ := finite_prior_reindex e μ F
  have h := bulk_distinctness_removal (fun i => μ (e i))
    (fun i => hμ (e i)) (fun i => hmass (e i)) α hα (fun i => hmax (e i))
    (fun x => F (x ∘ e.symm)) B hB (fun x => hF (x ∘ e.symm))
  change ‖(∑ x, ((∏ i, μ (e i) (x i) : ℝ) : ℂ) *
      (if Function.Injective x then F (x ∘ e.symm) else 0)) -
    ∑ x, ((∏ i, μ (e i) (x i) : ℝ) : ℂ) * F (x ∘ e.symm)‖ ≤ _ at h
  simp only [finite_univ_canonical] at he₁ he₂ h ⊢
  rw [he₁, he₂] at h
  exact h

theorem original_bulk_distinctness_removal_indexed {J : Type*} [Fintype J]
    (P : Finset ℕ) (Q : J → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (H T : ℝ) (hmass : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp H)
    (hlow : ∀ i p, p ∈ Q i → Real.exp T ≤ (p : ℝ))
    (F : (J → P) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ x : J → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
        (if Function.Injective x then F x else 0)) -
      ∑ x : J → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) * F x‖ ≤
      B * (Fintype.card J : ℝ) ^ 2 * Real.exp (H - T) := by
  have hmax (i : J) (p : P) : primeSubsetPrior P (Q i) p ≤ Real.exp (H - T) := by
    by_cases hp : (p : ℕ) ∈ Q i
    · exact primeSubsetPrior_le_exp P (Q i) p H T (hmass i) (hlow i p hp)
    · simpa only [primeSubsetPrior, hp, ite_false] using Real.exp_nonneg (H - T)
  have h := bulk_distinctness_removal_indexed (fun i => primeSubsetPrior P (Q i))
    (fun i p => primeSubsetPrior_nonneg P (Q i) p)
    (fun i => primeSubsetPrior_mass P (Q i) (hQP i) (hQ i))
    (Real.exp (H - T)) (Real.exp_nonneg _) hmax F B hB hF
  simp only [finite_univ_canonical] at h ⊢
  convert h using 1
  congr 2
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  split_ifs <;> rfl

end Ostmann

end OAI
