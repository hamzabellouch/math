import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.Finite

namespace OAI

namespace IndependentSetsGames.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem normalize_isProbability (b : α → ℝ) (hb : ∀ a, 0 ≤ b a)
    {B : ℝ} (hB : 0 < B) (hmass : ∑ a, b a = B) :
    IsProbability (fun a => b a / B) := by
  constructor
  · intro a
    exact div_nonneg (hb a) hB.le
  · simp only [div_eq_mul_inv, ← Finset.sum_mul, hmass, mul_inv_cancel₀ hB.ne']

theorem relativeEntropy_normalize_right (p b : α → ℝ) (hp : IsProbability p)
    (hs : SupportedBy p b) {B : ℝ} (hB : 0 < B) :
    relativeEntropy p (fun a => b a / B) = relativeEntropy p b + Real.log B := by
  have hpoint : ∀ a, p a * Real.log (p a / (b a / B)) =
      p a * Real.log (p a / b a) + p a * Real.log B := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    have hbne := hs a hpa
    rw [Real.log_div hpa (div_ne_zero hbne hB.ne'), Real.log_div hbne hB.ne',
      Real.log_div hpa hbne]
    ring
  simp only [relativeEntropy, hpoint, Finset.sum_add_distrib, ← Finset.sum_mul, hp.2, one_mul]

theorem neg_relativeEntropy_le_log_mass (p b : α → ℝ) (hp : IsProbability p)
    (hb : ∀ a, 0 ≤ b a) (hs : SupportedBy p b) {B : ℝ} (hB : 0 < B)
    (hmass : ∑ a, b a = B) : -relativeEntropy p b ≤ Real.log B := by
  have hs' : SupportedBy p (fun a => b a / B) :=
    fun a ha => div_ne_zero (hs a ha) hB.ne'
  have hnonneg := relativeEntropy_nonneg p (fun a => b a / B) hp
    (normalize_isProbability b hb hB hmass) hs'
  rw [relativeEntropy_normalize_right p b hp hs hB] at hnonneg
  linarith

theorem posterior_weighted_log_inverse_le (p b c : α → ℝ) (hp : IsProbability p)
    (hb : ∀ a, 0 ≤ b a) {z B : ℝ} (hz : 0 < z) (hB : 0 < B)
    (hmass : ∑ a, b a = B) (hpost : ∀ a, p a = b a * c a / z) :
    (∑ a, p a * Real.log (1 / c a)) ≤ Real.log (B / z) := by
  have hs : SupportedBy p b := by
    intro a ha hba
    apply ha
    rw [hpost, hba, zero_mul, zero_div]
  have hpoint : ∀ a, p a * Real.log (1 / c a) =
      p a * Real.log (1 / z) - p a * Real.log (p a / b a) := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    have hbne := hs a hpa
    have hcne : c a ≠ 0 := by
      intro hca
      apply hpa
      rw [hpost, hca, mul_zero, zero_div]
    have hratio : p a / b a = c a / z := by
      rw [hpost]
      field_simp [hbne, hz.ne']
    rw [hratio, Real.log_div hcne hz.ne', Real.log_div one_ne_zero hcne,
      Real.log_div one_ne_zero hz.ne', Real.log_one]
    ring
  have hid : (∑ a, p a * Real.log (1 / c a)) =
      Real.log (1 / z) - relativeEntropy p b := by
    simp only [hpoint, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul,
      relativeEntropy]
  have hkl := neg_relativeEntropy_le_log_mass p b hp hb hs hB hmass
  rw [hid, Real.log_div hB.ne' hz.ne', Real.log_div one_ne_zero hz.ne', Real.log_one]
  linarith

end IndependentSetsGames.Foundations.Information

end OAI
