import OAI.NumberTheory.JointDickman.Amplification.ArithmeticAmplification
import OAI.NumberTheory.JointDickman.Probability.QuotientSiteUnion

namespace OAI

/-! # Uniform bounds for the actual arithmetic amplification -/

namespace JointDickman
open Finset

open Classical in
noncomputable def arithmeticSiteWeight (B L : ℕ) (τ C : ℝ) (n : ℕ) : ℝ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset,
    if (∏ p ∈ A, p) ∣ n then
      regularCoefficientWeight B L τ C (∏ p ∈ A, p) *
        regularResidueWeight B L τ C (coefficientPrimeSet B (n / (∏ p ∈ A, p)))
    else 0

open Classical in
theorem arithmeticSiteWeight_nonneg (B L n : ℕ) (τ C : ℝ) :
    0 ≤ arithmeticSiteWeight B L τ C n := by
  apply sum_nonneg
  intro A _
  split_ifs
  · exact mul_nonneg (regularCoefficientWeight_nonneg ..) (regularResidueWeight_nonneg ..)
  · exact le_rfl

open Classical in
theorem arithmeticSiteWeight_le {B L n : ℕ} (τ C : ℝ) (hB : 1 < B) :
    arithmeticSiteWeight B L τ C n ≤ B := by
  let S := coefficientPrimeSet B n
  have hS : S ⊆ auxiliaryPrimes B := filter_subset _ _
  have hf : (auxiliaryPrimes B).powerset.filter (fun A => A ⊆ S) = S.powerset := by
    ext A
    simp only [mem_filter, mem_powerset]
    exact and_iff_right_of_imp (fun h => h.trans hS)
  calc
    _ ≤ ∑ A ∈ (auxiliaryPrimes B).powerset,
        if A ⊆ S then (B : ℝ) * (1 / 2 : ℝ)^S.card else 0 := by
      apply sum_le_sum
      intro A hA
      have hAP := mem_powerset.mp hA
      have he : A ⊆ S ↔ (∏ p ∈ A, p) ∣ n := (primeProduct_dvd_site_iff hAP).symm
      simp only [he]
      split_ifs with ha
      · exact arithmetic_split_weight_le hB hAP ha
      · exact le_rfl
    _ = (2 : ℝ)^S.card * ((B : ℝ) * (1 / 2 : ℝ)^S.card) := by
      rw [← sum_filter, hf]
      simp
    _ = B := by
      calc
        _ = (B : ℝ) * ((2 : ℝ) * (1 / 2))^S.card := by rw [mul_pow]; ring
        _ = _ := by norm_num

open Classical in
theorem arithmeticSubsetAmplification_nonneg (B L n : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (hw : ∀ a c, 0 ≤ w a c) :
    0 ≤ arithmeticSubsetAmplification B L τ C w n := by
  unfold arithmeticSubsetAmplification
  apply mul_nonneg (by positivity)
  apply sum_nonneg
  intro A _
  apply sum_nonneg
  intro D _
  split_ifs
  · exact mul_nonneg (mul_nonneg
      (mul_nonneg (regularCoefficientWeight_nonneg ..) (regularResidueWeight_nonneg ..))
      (mul_nonneg (regularCoefficientWeight_nonneg ..) (regularResidueWeight_nonneg ..))) (hw _ _)
  · exact le_rfl

open Classical in
theorem arithmeticSubsetAmplification_le {B L n : ℕ} (τ C : ℝ)
    (hB : 1 < B) (w : ℕ → ℕ → ℝ) (hw : ∀ a c, w a c ≤ 1) :
    arithmeticSubsetAmplification B L τ C w n ≤ B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hs := arithmeticSiteWeight_nonneg B L n τ C
  have ht := arithmeticSiteWeight_nonneg B L (n + 1) τ C
  calc
    _ ≤ (1 / (B : ℝ)) * (arithmeticSiteWeight B L τ C n *
        arithmeticSiteWeight B L τ C (n + 1)) := by
      unfold arithmeticSubsetAmplification arithmeticSiteWeight
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [sum_mul]
      simp only [mul_sum]
      apply sum_le_sum
      intro A _
      apply sum_le_sum
      intro D _
      split_ifs
      · exact mul_le_of_le_one_right (mul_nonneg
          (mul_nonneg (regularCoefficientWeight_nonneg ..) (regularResidueWeight_nonneg ..))
          (mul_nonneg (regularCoefficientWeight_nonneg ..) (regularResidueWeight_nonneg ..)))
          (hw _ _)
      all_goals simp_all only [and_self, and_true, and_false, mul_zero, zero_mul, not_true_eq_false, le_refl]
    _ ≤ (1 / (B : ℝ)) * ((B : ℝ) * B) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (arithmeticSiteWeight_le τ C hB) (arithmeticSiteWeight_le τ C hB)
          ht hB0.le) (by positivity)
    _ = B := by field_simp

end JointDickman

end OAI
