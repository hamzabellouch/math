import Mathlib.Analysis.Complex.Basic
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # Recombining the dyadic pieces of an original harmonic prime prior -/

namespace Ostmann

open scoped BigOperators Classical

theorem harmonic_raw_of_mean_bound (S : Finset ℕ) (F : ℕ → ℂ) (C : ℝ)
    (hm : 0 < ∑ p ∈ S, (p : ℝ)⁻¹)
    (h : ‖∑ p : S, (primeSubsetPrior S S p : ℂ) * F p‖ ^ 2 ≤
      (∑ p ∈ S, (p : ℝ)⁻¹)⁻¹ * C) :
    ‖∑ p ∈ S, ((p : ℝ)⁻¹ : ℂ) * F p‖ ^ 2 ≤ (∑ p ∈ S, (p : ℝ)⁻¹) * C := by
  rw [primeSubsetPrior_mean S S (Finset.Subset.refl _) F, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_of_nonneg hm.le, mul_pow] at h
  have ht := mul_le_mul_of_nonneg_left h (sq_nonneg (∑ p ∈ S, (p : ℝ)⁻¹))
  have h₁ : (∑ p ∈ S, (p : ℝ)⁻¹) ^ 2 * (∑ p ∈ S, (p : ℝ)⁻¹)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hm.ne', one_pow]
  have h₂ : (∑ p ∈ S, (p : ℝ)⁻¹) ^ 2 * (∑ p ∈ S, (p : ℝ)⁻¹)⁻¹ =
      ∑ p ∈ S, (p : ℝ)⁻¹ := by
    rw [pow_two, mul_assoc, mul_inv_cancel₀ hm.ne', mul_one]
  simpa only [← mul_assoc, h₁, h₂, one_mul] using ht

/-- The cost is the number of dyadic pieces, while the normalizer is the
original total harmonic mass. No lower bound for an individual piece is used. -/
theorem harmonic_partition_bound {I : Type*} [Fintype I]
    (P : Finset ℕ) (key : ℕ → I) (F : ℕ → ℂ) (C : ℝ)
    (hm : 0 < ∑ p ∈ P, (p : ℝ)⁻¹)
    (hlocal : ∀ i, ‖∑ p ∈ P.filter (fun p => key p = i), ((p : ℝ)⁻¹ : ℂ) * F p‖ ^ 2 ≤
      (∑ p ∈ P.filter (fun p => key p = i), (p : ℝ)⁻¹) * C) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) * F p‖ ^ 2 ≤
      (Fintype.card I : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ * C := by
  let z (i : I) : ℂ := ∑ p ∈ P.filter (fun p => key p = i), ((p : ℝ)⁻¹ : ℂ) * F p
  have hz : (∑ i, z i) = ∑ p ∈ P, ((p : ℝ)⁻¹ : ℂ) * F p :=
    Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
  have hmasses : (∑ i : I, ∑ p ∈ P.filter (fun p => key p = i), (p : ℝ)⁻¹) =
      ∑ p ∈ P, (p : ℝ)⁻¹ :=
    Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
  have hsq : ‖∑ i, z i‖ ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, ‖z i‖ ^ 2 := by
    have hn := norm_sum_le (Finset.univ : Finset I) z
    have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
      (fun _ => (1 : ℝ)) (fun i => ‖z i‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at hs
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs
  have hraw : ‖∑ p ∈ P, ((p : ℝ)⁻¹ : ℂ) * F p‖ ^ 2 ≤
      (Fintype.card I : ℝ) * ((∑ p ∈ P, (p : ℝ)⁻¹) * C) := by
    rw [← hz]
    apply hsq.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc
      _ ≤ ∑ i : I, (∑ p ∈ P.filter (fun p => key p = i), (p : ℝ)⁻¹) * C :=
        Finset.sum_le_sum fun i _ => hlocal i
      _ = _ := by rw [← Finset.sum_mul, hmasses]
  rw [primeSubsetPrior_mean P P (Finset.Subset.refl _) F, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_of_nonneg hm.le, mul_pow]
  have hh := mul_le_mul_of_nonneg_left hraw (sq_nonneg (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹)
  convert hh using 1
  field_simp

end Ostmann

end OAI
