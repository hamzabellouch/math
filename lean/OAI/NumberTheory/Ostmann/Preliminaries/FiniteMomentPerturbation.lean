import OAI.NumberTheory.Ostmann.Preliminaries.FiniteWitnessProbability

namespace OAI

/-! # Transferring first and second moments through the checked grid error -/

namespace Ostmann

open scoped BigOperators

theorem finite_mean_pointwise_le_add {ι : Type*} (S : Finset ι)
    (f g : ι → ℝ) (δ B : ℝ) (hδ : 0 ≤ δ)
    (hfg : ∀ i ∈ S, f i ≤ g i + δ)
    (hg : (S.card : ℝ)⁻¹ * (∑ i ∈ S, g i) ≤ B) :
    (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i) ≤ B + δ := by
  by_cases hS : S.Nonempty
  · have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
    have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hfg)
      (inv_nonneg.mpr (Nat.cast_nonneg S.card) : 0 ≤ (S.card : ℝ)⁻¹)
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_add] at hh
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at hh
    linarith
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hzero, Finset.sum_empty, mul_zero] at hg ⊢
    linarith

theorem finite_second_moment_pointwise_le_add {ι : Type*} (S : Finset ι)
    (f g : ι → ℝ) (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hf : ∀ i ∈ S, 0 ≤ f i) (hg : ∀ i ∈ S, 0 ≤ g i)
    (hfg : ∀ i ∈ S, f i ≤ g i + δ)
    (hsecond : (S.card : ℝ)⁻¹ * (∑ i ∈ S, g i ^ 2) ≤ B ^ 2) :
    (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i ^ 2) ≤ (B + δ) ^ 2 := by
  by_cases hS : S.Nonempty
  · have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
    have hmean := finite_mean_le_of_moment S g B 2 hB (by decide) hg hsecond
    have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi =>
      pow_le_pow_left₀ (hf i hi) (hfg i hi) 2))
      (inv_nonneg.mpr (Nat.cast_nonneg S.card) : 0 ≤ (S.card : ℝ)⁻¹)
    have hexpand : (∑ i ∈ S, (g i + δ) ^ 2) =
        (∑ i ∈ S, g i ^ 2) + 2 * δ * (∑ i ∈ S, g i) + (S.card : ℝ) * δ ^ 2 := by
      simp_rw [show ∀ x : ℝ, (x + δ) ^ 2 = x ^ 2 + 2 * δ * x + δ ^ 2 by intro x; ring]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    rw [hexpand, mul_add, mul_add] at hs
    have hcard : (S.card : ℝ)⁻¹ * ((S.card : ℝ) * δ ^ 2) = δ ^ 2 := by
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rw [hcard] at hs
    have hcross : (S.card : ℝ)⁻¹ * (2 * δ * (∑ i ∈ S, g i)) ≤ 2 * δ * B := by
      nlinarith [mul_le_mul_of_nonneg_left hmean (show 0 ≤ (2 : ℝ) * δ by positivity)]
    nlinarith
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [he, Finset.sum_empty, mul_zero]
    positivity

theorem finite_restricted_mean_pointwise_le_add {ι : Type*} (S E : Finset ι)
    (hES : E ⊆ S) (f g : ι → ℝ) (δ B : ℝ) (hδ : 0 ≤ δ)
    (hg : ∀ i ∈ S, 0 ≤ g i) (hfg : ∀ i ∈ E, f i ≤ g i + δ)
    (hmean : (S.card : ℝ)⁻¹ * (∑ i ∈ S, g i) ≤ B) :
    (S.card : ℝ)⁻¹ * (∑ i ∈ E, f i) ≤ B + δ := by
  have hs : (∑ i ∈ E, f i) ≤ ∑ i ∈ S, (g i + δ) :=
    (Finset.sum_le_sum hfg).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hES (fun i hi _ => add_nonneg (hg i hi) hδ))
  exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg _))).trans
    (finite_mean_pointwise_le_add S (fun i => g i + δ) g δ B hδ (fun _ _ => le_rfl) hmean)

end Ostmann

end OAI
