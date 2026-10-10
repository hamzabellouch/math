import OAI.NumberTheory.Ostmann.Construction.ScheduledAnchorMatchingCount
import OAI.NumberTheory.Ostmann.Construction.ScheduledHarmonicNormalization

namespace OAI

/-! # The original-prior cost of code-preserving matchings -/
namespace Ostmann
open scoped Classical BigOperators

theorem anchor_harmonic_entropy (r m : ℕ) (L z : ℝ)
    (hL : 0 < L) (hz : 0 < z) (hm : (m : ℝ) ≤ z * L) :
    ((2 * m : ℕ) : ℝ) ^ (r * m) * (L⁻¹) ^ (r * m) ≤
      Real.exp ((Real.log 2 + Real.log z) * (r * m : ℕ)) := by
  have hratio : (m : ℝ) * L⁻¹ ≤ z := by
    have hh := mul_le_mul_of_nonneg_right hm (inv_nonneg.mpr hL.le)
    simpa only [mul_assoc, mul_inv_cancel₀ hL.ne', mul_one] using hh
  have hbase : ((2 * m : ℕ) : ℝ) * L⁻¹ ≤ 2 * z := by
    push_cast
    nlinarith
  calc
    _ = (((2 * m : ℕ) : ℝ) * L⁻¹) ^ (r * m) := (mul_pow _ _ _).symm
    _ ≤ (2 * z) ^ (r * m) := pow_le_pow_left₀ (by positivity) hbase _
    _ = _ := by
      rw [← Real.exp_log (show 0 < 2 * z by positivity), ← Real.exp_nat_mul,
        Real.log_mul (by norm_num) hz.ne']
      congr 1
      ring

theorem scheduled_anchor_harmonic_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word})
    (mass : CopyScheduleH role n → ℝ) (L z : ℝ) (hL : 0 < L) (hz : 0 < z)
    (hm : (m : ℝ) ≤ z * L) (hmass : ∀ h, 0 < mass h)
    (hbulk : ∀ x, L ≤ mass (scheduledBulkCoordinates role n m word x).val) :
    ((scheduledAnchorMatchingSet role n m word).card : ℝ) * (∏ h, (mass h)⁻¹) ≤
      (Fintype.card (ScheduledNonbulkH role n)).factorial *
        (∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹) *
        Real.exp ((Real.log 2 + Real.log z) * (2 ^ n * m : ℕ)) := by
  let R : ℝ := ∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹
  have hR : 0 ≤ R := Finset.prod_nonneg (fun h _ => (inv_pos.mpr (hmass h.val)).le)
  have hc : ((scheduledAnchorMatchingSet role n m word).card : ℝ) ≤
      ((2 * m : ℕ) : ℝ) ^ (2 ^ n * m) *
        (Fintype.card (ScheduledNonbulkH role n)).factorial := by
    exact_mod_cast scheduledAnchorMatchingSet_card_le role n m word
  have hp := scheduled_harmonic_normalization_bound role n m word mass L hL hmass hbulk
  calc
    _ ≤ (((2 * m : ℕ) : ℝ) ^ (2 ^ n * m) *
        (Fintype.card (ScheduledNonbulkH role n)).factorial) *
        ((L⁻¹) ^ (2 ^ n * m) * R) :=
      mul_le_mul hc hp (Finset.prod_nonneg (fun h _ => (inv_pos.mpr (hmass h)).le)) (by positivity)
    _ = (Fintype.card (ScheduledNonbulkH role n)).factorial * R *
        (((2 * m : ℕ) : ℝ) ^ (2 ^ n * m) * (L⁻¹) ^ (2 ^ n * m)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (anchor_harmonic_entropy (2 ^ n) m L z hL hz hm)
      (mul_nonneg (by positivity) hR)

end Ostmann

end OAI
