import Mathlib.Analysis.MeanInequalitiesPow
import OAI.NumberTheory.Ostmann.Supply.PrimeSubsetProducts

namespace OAI

/-! # Passing from the finite even moment to expected absolute size -/

namespace Ostmann

open scoped BigOperators

theorem finite_mean_le_of_moment {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (B : ℝ) (m : ℕ) (hB : 0 ≤ B) (hm : 0 < m) (hf : ∀ i ∈ S, 0 ≤ f i)
    (h : (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i ^ m) ≤ B ^ m) :
    (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i) ≤ B := by
  by_cases hS : S.Nonempty
  · have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
    have hw : (∑ _i ∈ S, (S.card : ℝ)⁻¹) = 1 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_inv_cancel₀ hcard.ne'
    have hj := Real.pow_arith_mean_le_arith_mean_pow S (fun _ => (S.card : ℝ)⁻¹) f
      (fun _ _ => inv_nonneg.mpr hcard.le) hw hf m
    simp only [← Finset.mul_sum] at hj
    exact (pow_le_pow_iff_left₀
      (mul_nonneg (inv_nonneg.mpr hcard.le) (Finset.sum_nonneg hf)) hB hm.ne').mp (hj.trans h)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simpa only [he, Finset.card_empty, Nat.cast_zero, inv_zero, Finset.sum_empty,
      mul_zero] using hB

theorem prime_product_mean_le_of_moment (P : Finset ℕ) (k m : ℕ)
    (f : ℕ → ℂ) (B : ℝ) (hP : ∀ p ∈ P, p.Prime) (hB : 0 ≤ B) (hm : 0 < m)
    (h : (P.card.choose k : ℝ)⁻¹ * (∑ n ∈ primeSubsetProducts P k, ‖f n‖ ^ m) ≤ B ^ m) :
    (P.card.choose k : ℝ)⁻¹ * (∑ n ∈ primeSubsetProducts P k, ‖f n‖) ≤ B := by
  rw [← primeSubsetProducts_card P k hP] at h ⊢
  exact finite_mean_le_of_moment _ _ B m hB hm (fun _ _ => norm_nonneg _) h

end Ostmann

end OAI
