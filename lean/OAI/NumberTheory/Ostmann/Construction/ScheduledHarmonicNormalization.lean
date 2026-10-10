import OAI.NumberTheory.Ostmann.Construction.ScheduledBulkMatchingCount
import OAI.NumberTheory.Ostmann.Construction.BadMatchingHarmonicBudget

namespace OAI

/-! # The counterpart normalization for actual bulk and nonbulk slots -/

namespace Ostmann
open scoped Classical BigOperators

theorem scheduled_harmonic_normalization_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word})
    (mass : CopyScheduleH role n → ℝ) (L : ℝ) (hL : 0 < L)
    (hmass : ∀ h, 0 < mass h)
    (hbulk : ∀ x, L ≤ mass (scheduledBulkCoordinates role n m word x).val) :
    (∏ h, (mass h)⁻¹) ≤ (L⁻¹) ^ (2 ^ n * m) *
      ∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹ := by
  rw [← Equiv.prod_comp (scheduledSplitHCoordinates role n m word), Fintype.prod_sum_type]
  change (∏ x : Fin (2 ^ n) × Fin m, (mass (scheduledBulkCoordinates role n m word x).val)⁻¹) *
      (∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹) ≤ _
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun h _ => (inv_pos.mpr (hmass h.val)).le))
  calc
    _ ≤ ∏ _x : Fin (2 ^ n) × Fin m, L⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro x _; exact (inv_pos.mpr (hmass _)).le
      · intro x _; simpa only [one_div] using one_div_le_one_div_of_le hL (hbulk x)
    _ = _ := by simp

theorem scheduled_bad_matching_harmonic_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (hm0 : 0 < m)
    (mass : CopyScheduleH role n → ℝ) (L z C : ℝ) (hL : 0 < L) (hz : 0 < z)
    (hm : (m : ℝ) ≤ z * L) (hmass : ∀ h, 0 < mass h)
    (hbulk : ∀ x, L ≤ mass (scheduledBulkCoordinates role n m word x).val) :
    ((scheduledBadMatchingSet role n m word).card : ℝ) * (∏ h, (mass h)⁻¹) *
      Real.exp (C * (2 ^ n * m : ℕ)) ≤
      (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        (Fintype.card (ScheduledNonbulkH role n)).factorial *
        (∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹) *
        Real.exp ((Real.log z + Real.log (2 ^ n : ℕ) / 4 + C + 1 / 4) * (2 ^ n * m : ℕ)) := by
  let A : ℝ := (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ)
  let N : ℝ := (Fintype.card (ScheduledNonbulkH role n)).factorial
  let R : ℝ := ∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹
  have hR : 0 ≤ R := Finset.prod_nonneg (fun h _ => (inv_pos.mpr (hmass h.val)).le)
  have hc := scheduledBadMatchingSet_card_bound role n m word hm0
  have hp := scheduled_harmonic_normalization_bound role n m word mass L hL hmass hbulk
  have hf := factorial_harmonic_entropy (2 ^ n) m L z hL hz hm
  calc
    _ ≤ (A * (m.factorial : ℝ) ^ (2 ^ n) *
        Real.exp ((m : ℝ) * (2 ^ n : ℕ) * (Real.log (2 ^ n : ℕ) + 1) / 4) * N) *
        ((L⁻¹) ^ (2 ^ n * m) * R) * Real.exp (C * (2 ^ n * m : ℕ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul hc hp (Finset.prod_nonneg (fun h _ => (inv_pos.mpr (hmass h)).le)) (by positivity)
    _ = A * N * R * ((m.factorial : ℝ) ^ (2 ^ n) * (L⁻¹) ^ (2 ^ n * m)) *
        (Real.exp ((m : ℝ) * (2 ^ n : ℕ) * (Real.log (2 ^ n : ℕ) + 1) / 4) *
          Real.exp (C * (2 ^ n * m : ℕ))) := by ring
    _ ≤ A * N * R * Real.exp (Real.log z * (2 ^ n * m : ℕ)) *
        (Real.exp ((m : ℝ) * (2 ^ n : ℕ) * (Real.log (2 ^ n : ℕ) + 1) / 4) *
          Real.exp (C * (2 ^ n * m : ℕ))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hf (mul_nonneg (by positivity) hR)
    _ = _ := by
      dsimp only [A, N, R]
      simp only [mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      push_cast
      ring_nf

end Ostmann

end OAI
