import OAI.NumberTheory.Ostmann.Preliminaries.FiniteMomentPerturbation

namespace OAI

/-! # Transferring a finite inner sum to its largest covered term -/

namespace Ostmann

open scoped BigOperators

/-- The index type need not be inhabited: if it has no covered term, every
inner sum is empty. The bound is uniform over adaptive choices of indices. -/
theorem finite_inner_sum_mean_le {α β ι : Type*} [DecidableEq β]
    (A : Finset α) (D : α → Finset β) (f : α → β → ℝ) (g : α → ι → ℝ)
    (C δ B : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hf : ∀ a ∈ A, ∀ b ∈ D a, 0 ≤ f a b)
    (hg : ∀ a ∈ A, ∀ i, 0 ≤ g a i)
    (hcard : ∀ a ∈ A, ((D a).card : ℝ) ≤ C)
    (hcover : ∀ a ∈ A, ∀ b ∈ D a, ∃ i, f a b ≤ g a i + δ)
    (hmean : ∀ pick : α → ι,
      (A.card : ℝ)⁻¹ * (∑ a ∈ A, g a (pick a)) ≤ B) :
    (A.card : ℝ)⁻¹ * (∑ a ∈ A, ∑ b ∈ D a, f a b) ≤ C * (B + δ) := by
  classical
  by_cases hex : ∃ a ∈ A, (D a).Nonempty
  · obtain ⟨a₀, ha₀, b₀, hb₀⟩ := hex
    obtain ⟨i₀, _⟩ := hcover a₀ ha₀ b₀ hb₀
    have hpick (a : α) : ∃ i, a ∈ A →
        (∑ b ∈ D a, f a b) ≤ C * (g a i + δ) := by
      by_cases ha : a ∈ A
      · by_cases hd : (D a).Nonempty
        · obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image (D a) (f a) hd
          obtain ⟨i, hi⟩ := hcover a ha b hb
          refine ⟨i, fun _ => ?_⟩
          calc
            (∑ d ∈ D a, f a d) ≤ (D a).card * f a b := by
              simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul (D a) (f a) (f a b) hmax
            _ ≤ C * f a b := mul_le_mul_of_nonneg_right (hcard a ha) (hf a ha b hb)
            _ ≤ C * (g a i + δ) := mul_le_mul_of_nonneg_left hi hC
        · refine ⟨i₀, fun _ => ?_⟩
          rw [Finset.not_nonempty_iff_eq_empty.mp hd, Finset.sum_empty]
          exact mul_nonneg hC (add_nonneg (hg a ha i₀) hδ)
      · exact ⟨i₀, fun h => (ha h).elim⟩
    choose pick hp using hpick
    have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a ha => hp a ha))
      (inv_nonneg.mpr (Nat.cast_nonneg A.card) : 0 ≤ (A.card : ℝ)⁻¹)
    rw [← Finset.mul_sum] at hs
    have he := finite_mean_pointwise_le_add A (fun a => g a (pick a) + δ)
      (fun a => g a (pick a)) δ B hδ (fun _ _ => le_rfl) (hmean pick)
    nlinarith [mul_le_mul_of_nonneg_left he hC]
  · have hempty (a : α) (ha : a ∈ A) : D a = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      exact fun h => hex ⟨a, ha, h⟩
    have hz : (∑ a ∈ A, ∑ b ∈ D a, f a b) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [hempty a ha, Finset.sum_empty]
    rw [hz, mul_zero]
    exact mul_nonneg hC (add_nonneg hB hδ)

end Ostmann

end OAI
