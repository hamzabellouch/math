import OAI.NumberTheory.Ostmann.Tree.SmallDepthMatchingCount
import OAI.NumberTheory.Ostmann.Construction.ScheduledHarmonicNormalization

namespace OAI

/-! # The bad-diagonal harmonic budget, including the first two levels -/

namespace Ostmann
open scoped Classical BigOperators

theorem scheduled_diagonal_bad_harmonic_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (hm0 : 0 < m)
    (mass : CopyScheduleH role n → ℝ) (L z C : ℝ) (hL : 0 < L) (hz : 0 < z)
    (hm : (m : ℝ) ≤ z * L) (hmass : ∀ h, 0 < mass h)
    (hbulk : ∀ x, L ≤ mass (scheduledBulkCoordinates role n m word x).val) :
    ((scheduledDiagonalBadMatchingSet role n m word).card : ℝ) * (∏ h, (mass h)⁻¹) *
      Real.exp (C * (2 ^ n * m : ℕ)) ≤
      (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        (Fintype.card (ScheduledNonbulkH role n)).factorial *
        (∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹) *
        Real.exp ((Real.log z + Real.log (2 ^ n : ℕ) / 4 + C + 2) * (2 ^ n * m : ℕ)) := by
  let A : ℝ := (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ)
  let N : ℝ := (Fintype.card (ScheduledNonbulkH role n)).factorial
  let R : ℝ := ∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹
  have hR : 0 ≤ R := Finset.prod_nonneg (fun h _ => (inv_pos.mpr (hmass h.val)).le)
  have hc := scheduledDiagonalBadMatchingSet_card_bound role n m word hm0
  have hp := scheduled_harmonic_normalization_bound role n m word mass L hL hmass hbulk
  have hf := factorial_harmonic_entropy (2 ^ n) m L z hL hz hm
  calc
    _ ≤ (A * (m.factorial : ℝ) ^ (2 ^ n) *
        Real.exp (((2 ^ n * m : ℕ) : ℝ) * (Real.log (2 ^ n : ℕ) / 4 + 2)) * N) *
        ((L⁻¹) ^ (2 ^ n * m) * R) * Real.exp (C * (2 ^ n * m : ℕ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul hc hp (Finset.prod_nonneg (fun h _ => (inv_pos.mpr (hmass h)).le)) (by positivity)
    _ = A * N * R * ((m.factorial : ℝ) ^ (2 ^ n) * (L⁻¹) ^ (2 ^ n * m)) *
        (Real.exp (((2 ^ n * m : ℕ) : ℝ) * (Real.log (2 ^ n : ℕ) / 4 + 2)) *
          Real.exp (C * (2 ^ n * m : ℕ))) := by ring
    _ ≤ A * N * R * Real.exp (Real.log z * (2 ^ n * m : ℕ)) *
        (Real.exp (((2 ^ n * m : ℕ) : ℝ) * (Real.log (2 ^ n : ℕ) / 4 + 2)) *
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
