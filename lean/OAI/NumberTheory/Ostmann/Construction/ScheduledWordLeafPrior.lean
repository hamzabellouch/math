import OAI.NumberTheory.Ostmann.Construction.ScheduledWordLeafCoordinates

namespace OAI

/-! # Conditioning on all primes except the selected original word leaves -/

namespace Ostmann
open scoped BigOperators Classical

theorem scheduled_wordLeaf_sum {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (μ : I → A → ℝ) (F : (CopyScheduleAtoms role n → A) → ℝ) :
    (∑ q, scheduledPrimePrior role n μ q * F q) =
      ∑ y : WordLeafOutside role i hi n → A,
        (∏ v : WordLeafOutside role i hi n, μ (copyScheduleOrigin n v.val.val) (y v)) *
          ∑ x : TreeLeafIndex n → A, (∏ t, μ i (x t)) *
            F (wordLeafAssignment role i hi n y x) := by
  rw [← (wordLeafAssignmentEquiv (A := A) role i hi n).sum_comp
    (fun q => scheduledPrimePrior role n μ q * F q)]
  simp only [Fintype.sum_prod_type, wordLeafAssignmentEquiv]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  change scheduledPrimePrior role n μ (wordLeafAssignment role i hi n y x) *
    F (wordLeafAssignment role i hi n y x) = _
  rw [scheduledPrimePrior_wordLeaf]
  ring

/-- A bound for each fixed assignment of the remaining primes averages
without any loss. The selected 2^n prime marginals remain the original ones. -/
theorem scheduled_wordLeaf_sum_le {I A D : Type*}
    [Fintype I] [Fintype A] [Fintype D]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (μ : I → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a) (hmass : ∀ j, ∑ a, μ j a = 1)
    (F : D → (CopyScheduleAtoms role n → A) → ℝ) (B : ℝ)
    (hsection : ∀ y : WordLeafOutside role i hi n → A,
      (∑ d, ∑ x : TreeLeafIndex n → A, (∏ t, μ i (x t)) *
        F d (wordLeafAssignment role i hi n y x)) ≤ B) :
    (∑ d, ∑ q, scheduledPrimePrior role n μ q * F d q) ≤ B := by
  have hm : (∑ y : WordLeafOutside role i hi n → A,
      ∏ v : WordLeafOutside role i hi n, μ (copyScheduleOrigin n v.val.val) (y v)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [hmass, Finset.prod_const_one]
  simp_rw [scheduled_wordLeaf_sum role i hi n μ]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ y : WordLeafOutside role i hi n → A,
        (∏ v : WordLeafOutside role i hi n, μ (copyScheduleOrigin n v.val.val) (y v)) * B := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hsection y)
        (Finset.prod_nonneg (fun v _ => hμ _ _))
    _ = B := by rw [← Finset.sum_mul, hm, one_mul]

end Ostmann

end OAI
