import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.Pigeonhole
import OAI.NumberTheory.Ostmann.Construction.FiniteProductPrior

namespace OAI

/-! # Positive word means and a common product bin -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def binnedWordAverage {A B : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (F : Fin n → A → ℂ) (bin : (Fin n → A) → B) (b : B) : ℂ :=
  ∑ x, if bin x = b then (productPrior μ x : ℂ) * ∏ i, F i (x i) else 0

theorem binnedWordAverage_sum {A B : Type*} [Fintype A] [Fintype B] {n : ℕ}
    (μ : Fin n → A → ℝ) (F : Fin n → A → ℂ) (bin : (Fin n → A) → B) :
    (∑ b, binnedWordAverage μ F bin b) = ∏ i, ∑ a, (μ i a : ℂ) * F i a := by
  unfold binnedWordAverage
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [productPrior, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin n) (a : A) => (μ i a : ℂ) * F i a)).symm

/-- Independent positive real means give a large total word mean before
choosing any product bin. -/
theorem binnedWordAverage_total_lower {A B : Type*} [Fintype A] [Fintype B] {n : ℕ}
    (μ : Fin n → A → ℝ) (F : Fin n → A → ℂ) (bin : (Fin n → A) → B)
    (δ : ℝ) (hδ : 0 ≤ δ) (hmean : ∀ i, δ ≤ (∑ a, (μ i a : ℂ) * F i a).re) :
    δ ^ n ≤ ‖∑ b, binnedWordAverage μ F bin b‖ := by
  rw [binnedWordAverage_sum, norm_prod]
  calc
    δ ^ n = ∏ _i : Fin n, δ := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hδ)
      (fun i _ => (hmean i).trans (Complex.re_le_norm _))

/-- A finite product-bin partition retains a large coefficient in at least
one bin. -/
theorem exists_large_complex_bin {B : Type*} [Fintype B] [Nonempty B]
    (v : B → ℂ) : ∃ b, ‖∑ j, v j‖ ≤ (Fintype.card B : ℝ) * ‖v b‖ := by
  obtain ⟨b, _, hb⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖) Finset.univ_nonempty
  refine ⟨b, (norm_sum_le _ _).trans ?_⟩
  calc
    (∑ j, ‖v j‖) ≤ ∑ _j : B, ‖v b‖ := Finset.sum_le_sum (fun j hj => hb j hj)
    _ = _ := by simp

theorem exists_large_word_bin {A B : Type*} [Fintype A] [Fintype B] [Nonempty B] {n : ℕ}
    (μ : Fin n → A → ℝ) (F : Fin n → A → ℂ) (bin : (Fin n → A) → B)
    (δ : ℝ) (hδ : 0 ≤ δ) (hmean : ∀ i, δ ≤ (∑ a, (μ i a : ℂ) * F i a).re) :
    ∃ b, δ ^ n ≤ (Fintype.card B : ℝ) * ‖binnedWordAverage μ F bin b‖ := by
  obtain ⟨b, hb⟩ := exists_large_complex_bin (binnedWordAverage μ F bin)
  exact ⟨b, (binnedWordAverage_total_lower μ F bin δ hδ hmean).trans hb⟩

/-- A single bin works on a proportionate set of the actual endpoints. -/
theorem common_large_bin {B : Type*} [Fintype B] [Nonempty B]
    (E : Finset ℕ) (v : ℕ → B → ℂ) (η : ℝ)
    (hE : ∀ a ∈ E, η ≤ ‖∑ b, v a b‖) :
    ∃ b, ∃ S : Finset ℕ, S ⊆ E ∧ E.card ≤ Fintype.card B * S.card ∧
      ∀ a ∈ S, η ≤ (Fintype.card B : ℝ) * ‖v a b‖ := by
  have hex : ∀ a : ℕ, ∃ b, ‖∑ j, v a j‖ ≤ (Fintype.card B : ℝ) * ‖v a b‖ :=
    fun a => exists_large_complex_bin (v a)
  choose b hb using hex
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
    (fun j => (E.filter (fun a => b a = j)).card) Finset.univ_nonempty
  refine ⟨j, E.filter (fun a => b a = j), Finset.filter_subset _ _, ?_, ?_⟩
  · calc
      E.card = ∑ j : B, (E.filter (fun a => b a = j)).card := by
        simpa using (Finset.card_eq_sum_card_fiberwise (s := E) (t := Finset.univ) (fun a _ => Finset.mem_univ (b a)))
      _ ≤ ∑ _j : B, (E.filter (fun a => b a = j)).card :=
        Finset.sum_le_sum (fun k hk => hj k hk)
      _ = _ := by simp
  · intro a ha
    obtain ⟨haE, haj⟩ := Finset.mem_filter.mp ha
    exact (hE a haE).trans (by simpa [haj] using hb a)

/-- Every bin coefficient remains bounded by one under the original
probability law; restricting a bin does not renormalize that law. -/
theorem binnedWordAverage_norm_le_one {A B : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (F : Fin n → A → ℂ) (bin : (Fin n → A) → B) (b : B)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (hF : ∀ i a, ‖F i a‖ ≤ 1) : ‖binnedWordAverage μ F bin b‖ ≤ 1 := by
  unfold binnedWordAverage
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ x, productPrior μ x := by
      apply Finset.sum_le_sum
      intro x _
      have hx := productPrior_nonneg μ hμ x
      split_ifs
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
        apply mul_le_of_le_one_right hx
        rw [norm_prod]
        exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hF i (x i))
      · simpa using hx
    _ = 1 := productPrior_mass μ hmass

end Ostmann

end OAI
