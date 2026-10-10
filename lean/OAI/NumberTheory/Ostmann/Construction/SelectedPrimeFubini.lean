import Mathlib.Logic.Equiv.Set
import OAI.NumberTheory.Ostmann.Construction.FiniteCoordinatePrior
import OAI.NumberTheory.Ostmann.Construction.FiniteEnumeration
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # Exact bulk and nonbulk decomposition of the original finite prime law -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedIndexEquiv {σ J : Type*} (slot : J ↪ σ) :
    J ⊕ {i : σ // i ∉ Set.range slot} ≃ σ :=
  (Equiv.sumCongr (Equiv.ofInjective slot slot.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun i => i ∈ Set.range slot))

@[simp] theorem selectedIndexEquiv_inl {σ J : Type*} (slot : J ↪ σ) (j : J) :
    selectedIndexEquiv slot (.inl j) = slot j := rfl

@[simp] theorem selectedIndexEquiv_inr {σ J : Type*} (slot : J ↪ σ)
    (i : {i : σ // i ∉ Set.range slot}) : selectedIndexEquiv slot (.inr i) = i := rfl

noncomputable def joinBulkNonbulk {σ J A : Type*} (slot : J ↪ σ)
    (bulk : J → A) (nonbulk : {i : σ // i ∉ Set.range slot} → A) : σ → A :=
  Sum.elim bulk nonbulk ∘ (selectedIndexEquiv slot).symm

@[simp] theorem joinBulkNonbulk_bulk {σ J A : Type*} (slot : J ↪ σ)
    (bulk : J → A) (nonbulk : {i : σ // i ∉ Set.range slot} → A) (j : J) :
    joinBulkNonbulk slot bulk nonbulk (slot j) = bulk j := by
  change Sum.elim bulk nonbulk ((selectedIndexEquiv slot).symm (selectedIndexEquiv slot (.inl j))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem joinBulkNonbulk_nonbulk {σ J A : Type*} (slot : J ↪ σ)
    (bulk : J → A) (nonbulk : {i : σ // i ∉ Set.range slot} → A)
    (i : {i : σ // i ∉ Set.range slot}) : joinBulkNonbulk slot bulk nonbulk i = nonbulk i := by
  change Sum.elim bulk nonbulk ((selectedIndexEquiv slot).symm (selectedIndexEquiv slot (.inr i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem finite_prior_selected_fubini {σ J A : Type*}
    [Fintype σ] [Fintype J] [Fintype A]
    (slot : J ↪ σ) (μ : σ → A → ℝ) (F : (σ → A) → ℂ) :
    (∑ x : σ → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x) =
      ∑ y : {i : σ // i ∉ Set.range slot} → A,
        ((∏ i : {i : σ // i ∉ Set.range slot}, μ i (y i) : ℝ) : ℂ) *
          ∑ x : J → A, ((∏ j, μ (slot j) (x j) : ℝ) : ℂ) * F (joinBulkNonbulk slot x y) := by
  rw [← finite_prior_reindex (selectedIndexEquiv slot) μ F]
  let e := Equiv.sumArrowEquivProdArrow J {i : σ // i ∉ Set.range slot} A
  have he := e.symm.sum_comp (fun x =>
    ((∏ i, μ (selectedIndexEquiv slot i) (x i) : ℝ) : ℂ) *
      F (x ∘ (selectedIndexEquiv slot).symm))
  simp only [finite_univ_canonical] at he ⊢
  rw [← he]
  have hs := Fintype.sum_prod_type (fun x : (J → A) × ({i : σ // i ∉ Set.range slot} → A) =>
    ((∏ i, μ (selectedIndexEquiv slot i) (e.symm x i) : ℝ) : ℂ) *
      F (e.symm x ∘ (selectedIndexEquiv slot).symm))
  simp only [finite_univ_canonical] at hs
  rw [hs, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hp := Fintype.prod_sum_type (fun i : J ⊕ {i : σ // i ∉ Set.range slot} =>
    μ (selectedIndexEquiv slot i) (e.symm (x, y) i))
  simp only [finite_univ_canonical] at hp
  rw [hp]
  simp only [selectedIndexEquiv_inl, selectedIndexEquiv_inr,
    e, Equiv.sumArrowEquivProdArrow_symm_apply_inl, Equiv.sumArrowEquivProdArrow_symm_apply_inr,
    Complex.ofReal_mul]
  change _ * F (joinBulkNonbulk slot x y) = _
  ring

/-- Variable nonbulk majorants are integrated with their original weights. -/
theorem finite_prior_selected_majorant {σ J A : Type*}
    [Fintype σ] [Fintype J] [Fintype A]
    (slot : J ↪ σ) (μ : σ → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (F : (σ → A) → ℂ) (B : ({i : σ // i ∉ Set.range slot} → A) → ℝ)
    (hF : ∀ y : {i : σ // i ∉ Set.range slot} → A,
      (∀ i : {i : σ // i ∉ Set.range slot}, μ i (y i) ≠ 0) →
      ‖∑ x : J → A, ((∏ j, μ (slot j) (x j) : ℝ) : ℂ) * F (joinBulkNonbulk slot x y)‖ ≤ B y) :
    ‖∑ x : σ → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x‖ ≤
      ∑ y : {i : σ // i ∉ Set.range slot} → A,
        (∏ i : {i : σ // i ∉ Set.range slot}, μ i (y i)) * B y := by
  rw [finite_prior_selected_fubini slot μ F]
  apply norm_sum_le_of_le
  intro y _
  by_cases hz : (∏ i : {i : σ // i ∉ Set.range slot}, μ i (y i)) = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul, norm_zero, le_refl]
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (Finset.prod_nonneg fun (i : {i : σ // i ∉ Set.range slot}) _ => hμ i (y i))]
    exact mul_le_mul_of_nonneg_left (hF y (fun (i : {i : σ // i ∉ Set.range slot}) =>
      Finset.prod_ne_zero_iff.mp hz i (Finset.mem_univ i)))
      (Finset.prod_nonneg fun (i : {i : σ // i ∉ Set.range slot}) _ => hμ i (y i))

/-- Uniform bounds for the literal selected-bulk means pass to the full
original law, without introducing a conditional independence assumption. -/
theorem finite_prior_selected_bound {σ J A : Type*}
    [Fintype σ] [Fintype J] [Fintype A]
    (slot : J ↪ σ) (μ : σ → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1) (F : (σ → A) → ℂ) (B : ℝ)
    (hF : ∀ y : {i : σ // i ∉ Set.range slot} → A,
      (∀ i : {i : σ // i ∉ Set.range slot}, μ i (y i) ≠ 0) →
      ‖∑ x : J → A, ((∏ j, μ (slot j) (x j) : ℝ) : ℂ) * F (joinBulkNonbulk slot x y)‖ ≤ B) :
    ‖∑ x : σ → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x‖ ≤ B := by
  rw [finite_prior_selected_fubini slot μ F]
  calc
    _ ≤ ∑ y : {i : σ // i ∉ Set.range slot} → A, (∏ i : {i : σ // i ∉ Set.range slot}, μ i (y i)) * B := by
      apply norm_sum_le_of_le
      intro y _
      by_cases hz : (∏ i : {i : σ // i ∉ Set.range slot}, μ i (y i)) = 0
      · simp only [hz, Complex.ofReal_zero, zero_mul, norm_zero, le_refl]
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
          (Finset.prod_nonneg fun (i : {i : σ // i ∉ Set.range slot}) _ => hμ i (y i))]
        exact mul_le_mul_of_nonneg_left (hF y (fun (i : {i : σ // i ∉ Set.range slot}) =>
          Finset.prod_ne_zero_iff.mp hz i (Finset.mem_univ i)))
          (Finset.prod_nonneg fun (i : {i : σ // i ∉ Set.range slot}) _ => hμ i (y i))
    _ = B := by
      rw [← Finset.sum_mul, ← Fintype.prod_sum]
      simp only [hmass, Finset.prod_const_one, one_mul]

theorem original_prime_selected_bound {σ J : Type*} [Fintype σ] [Fintype J]
    (P : Finset ℕ) (Q : σ → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (slot : J ↪ σ) (F : (σ → P) → ℂ) (B : ℝ)
    (hF : ∀ y : {i : σ // i ∉ Set.range slot} → P,
      (∀ i : {i : σ // i ∉ Set.range slot}, (y i : ℕ) ∈ Q i) →
      ‖∑ x : J → P, ((∏ j, primeSubsetPrior P (Q (slot j)) (x j) : ℝ) : ℂ) *
        F (joinBulkNonbulk slot x y)‖ ≤ B) :
    ‖∑ x : σ → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) * F x‖ ≤ B := by
  apply finite_prior_selected_bound slot (fun i => primeSubsetPrior P (Q i))
    (fun i p => primeSubsetPrior_nonneg P (Q i) p)
    (fun i => primeSubsetPrior_mass P (Q i) (hQP i) (hQ i)) F B
  intro y hy
  exact hF y (fun (i : {i : σ // i ∉ Set.range slot}) => primeSubsetPrior_support P (Q i) (y i) (hy i))

theorem original_prime_selected_majorant {σ J : Type*} [Fintype σ] [Fintype J]
    (P : Finset ℕ) (Q : σ → Finset ℕ) (slot : J ↪ σ) (F : (σ → P) → ℂ)
    (B : ({i : σ // i ∉ Set.range slot} → P) → ℝ)
    (hF : ∀ y : {i : σ // i ∉ Set.range slot} → P,
      (∀ i : {i : σ // i ∉ Set.range slot}, (y i : ℕ) ∈ Q i) →
      ‖∑ x : J → P, ((∏ j, primeSubsetPrior P (Q (slot j)) (x j) : ℝ) : ℂ) *
        F (joinBulkNonbulk slot x y)‖ ≤ B y) :
    ‖∑ x : σ → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) * F x‖ ≤
      ∑ y : {i : σ // i ∉ Set.range slot} → P,
        (∏ i : {i : σ // i ∉ Set.range slot}, primeSubsetPrior P (Q i) (y i)) * B y := by
  apply finite_prior_selected_majorant slot (fun i => primeSubsetPrior P (Q i))
    (fun i p => primeSubsetPrior_nonneg P (Q i) p) F B
  intro y hy
  exact hF y (fun (i : {i : σ // i ∉ Set.range slot}) =>
    primeSubsetPrior_support P (Q i) (y i) (hy i))

theorem joinBulkNonbulk_eq_extend {σ J A : Type*} (slot : J ↪ σ)
    (bulk : J → A) (nonbulk : {i : σ // i ∉ Set.range slot} → A)
    (base : σ → A) (hbase : ∀ i : {i : σ // i ∉ Set.range slot}, base i = nonbulk i) :
    joinBulkNonbulk slot bulk nonbulk = Function.extend slot bulk base := by
  funext i
  by_cases hi : ∃ j, slot j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [joinBulkNonbulk_bulk, slot.injective.extend_apply]
  · rw [show joinBulkNonbulk slot bulk nonbulk i = nonbulk ⟨i, hi⟩ from
        joinBulkNonbulk_nonbulk slot bulk nonbulk ⟨i, hi⟩,
      Function.extend_apply' _ base i hi, hbase ⟨i, hi⟩]

end Ostmann

end OAI
