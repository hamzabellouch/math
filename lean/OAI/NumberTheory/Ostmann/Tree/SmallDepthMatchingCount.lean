import OAI.NumberTheory.Ostmann.Construction.ConstituentDiagonalSupport
import OAI.NumberTheory.Ostmann.Tree.ComponentFactorial

namespace OAI

/-! # The first two diagonals treat every matching as bad -/

namespace Ostmann
open scoped Classical

noncomputable def scheduledDiagonalBadMatchingSet {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) : Finset (Equiv.Perm (CopyScheduleH role n)) :=
  if n < 2 then cellPreservingMatchings (scheduledBulkLabel role n)
  else scheduledBadMatchingSet role n m word

theorem scheduledDiagonalBadMatchingSet_subset {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) :
    scheduledDiagonalBadMatchingSet role n m word ⊆
      cellPreservingMatchings (scheduledBulkLabel role n) := by
  unfold scheduledDiagonalBadMatchingSet
  split_ifs
  · exact Finset.Subset.refl _
  · exact scheduledBadMatchingSet_subset role n m word

theorem scheduled_cellPreserving_card_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) :
    (cellPreservingMatchings (scheduledBulkLabel role n)).card ≤
      (2 ^ n * m).factorial * (Fintype.card (ScheduledNonbulkH role n)).factorial := by
  have hc : (cellPreservingMatchings (scheduledBulkLabel role n)).card =
      Fintype.card (PartitionMatching (scheduledBulkLabel role n) (scheduledBulkLabel role n)) := by
    calc
      _ = Fintype.card ↥(cellPreservingMatchings (scheduledBulkLabel role n)) :=
        (Fintype.card_coe _).symm
      _ = _ := by
        let E : ↥(cellPreservingMatchings (scheduledBulkLabel role n)) ≃
            PartitionMatching (scheduledBulkLabel role n) (scheduledBulkLabel role n) := {
          toFun := fun e => ⟨e.val, (mem_cellPreservingMatchings _ _).mp e.property⟩
          invFun := fun e => ⟨e.val, (mem_cellPreservingMatchings _ _).mpr e.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
        exact Fintype.card_congr E

  rw [hc]
  have h₁ := Fintype.card_le_of_injective _ (scheduledSeparatedMatching_injective role n m word)
  have h₂ := Fintype.card_le_of_injective _
    (separatedMatching_pair_injective (A := Fin (2 ^ n) × Fin m) (B := ScheduledNonbulkH role n))
  exact (h₁.trans h₂).trans_eq (by simp only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin])

theorem small_depth_matching_count {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (hn : n < 2) :
    ((cellPreservingMatchings (scheduledBulkLabel role n)).card : ℝ) ≤
      (m.factorial : ℝ) ^ (2 ^ n) * Real.exp (2 * (2 ^ n * m : ℕ)) *
        (Fintype.card (ScheduledNonbulkH role n)).factorial := by
  have hr : (2 ^ n : ℕ) ≤ 2 := by interval_cases n <;> norm_num
  have hp : (2 ^ n : ℝ) ≤ Real.exp 2 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    have hr' : (2 ^ n : ℝ) ≤ 2 := by exact_mod_cast hr
    linarith
  have hf : ((2 ^ n * m).factorial : ℝ) ≤
      (m.factorial : ℝ) ^ (2 ^ n) * Real.exp (2 * (2 ^ n * m : ℕ)) := by
    have h := (Nat.cast_le (α := ℝ)).mpr (component_factorial_le (2 ^ n) m)
    push_cast at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ (Real.exp 2) ^ (2 ^ n * m) := pow_le_pow_left₀ (by positivity) hp _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hc := (Nat.cast_le (α := ℝ)).mpr (scheduled_cellPreserving_card_bound role n m word)
  push_cast at hc
  exact hc.trans (mul_le_mul_of_nonneg_right hf (by positivity))

theorem scheduledDiagonalBadMatchingSet_card_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (hm : 0 < m) :
    ((scheduledDiagonalBadMatchingSet role n m word).card : ℝ) ≤
      (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        (m.factorial : ℝ) ^ (2 ^ n) *
        Real.exp (((2 ^ n * m : ℕ) : ℝ) * (Real.log (2 ^ n : ℕ) / 4 + 2)) *
        (Fintype.card (ScheduledNonbulkH role n)).factorial := by
  have hlog : 0 ≤ Real.log (2 ^ n : ℕ) := Real.log_nonneg (by exact_mod_cast Nat.one_le_two_pow)
  have hA : (1 : ℝ) ≤ (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) := by
    have ha : 0 < ((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) := by positivity
    exact_mod_cast Nat.succ_le_of_lt ha
  unfold scheduledDiagonalBadMatchingSet
  split_ifs with hn
  · apply (small_depth_matching_count role n m word hn).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul (le_mul_of_one_le_left (by positivity) hA)
      (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
    convert mul_le_mul_of_nonneg_left (show 2 ≤ Real.log (2 ^ n : ℕ) / 4 + 2 by linarith)
      (show (0 : ℝ) ≤ (2 ^ n * m : ℕ) from Nat.cast_nonneg _) using 1; ring
  · apply (scheduledBadMatchingSet_card_bound role n m word hm).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    push_cast
    calc
      _ = ((m : ℝ) * (2 : ℝ) ^ n) * (Real.log ((2 : ℝ) ^ n) / 4 + 1 / 4) := by ring
      _ ≤ ((m : ℝ) * (2 : ℝ) ^ n) * (Real.log ((2 : ℝ) ^ n) / 4 + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring

end Ostmann

end OAI
