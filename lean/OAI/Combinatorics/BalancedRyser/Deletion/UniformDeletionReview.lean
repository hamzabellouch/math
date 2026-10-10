import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.BalancedRyser.Deletion.UniformDeletionMoments

namespace OAI

open scoped BigOperators
open _root_.Balanced _root_.OAI.Balanced Balanced.UniformDeletion

example {F : Type*} [Field F] [Fintype F] [DecidableEq F] (p : Point F) :
    deletionEventProbability (law 0 (Nat.zero_le (Fintype.card F)))
      (fun D => p ∈ uncoveredBy D.val) = 1 := by
  rw [point_survival_eq]
  norm_num

example {F : Type*} [Field F] [Fintype F] [DecidableEq F] (p : Point F) :
    deletionEventProbability (law (Fintype.card F) le_rfl)
      (fun D => p ∈ uncoveredBy D.val) = 0 := by
  rw [point_survival_eq]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := F)).ne'
  simp [hq]

example :
    (∑ D, (law (F := ZMod 2) 1 (by norm_num) D).toReal *
      ((uncoveredBy D.val).card : ℝ)) = 1 / 2 := by
  rw [expected_core_card]
  norm_num

example :
    (∑ D, (law (F := ZMod 2) 1 (by norm_num) D).toReal *
      (((uncoveredBy D.val).card : ℝ) ^ 2)) = 1 / 2 := by
  rw [expected_core_sq]
  norm_num

example :
    (∑ D, (law (F := ZMod 3) 1 (by norm_num) D).toReal *
      (((uncoveredBy D.val).card : ℝ) ^ 2)) = 32 / 9 := by
  rw [expected_core_sq]
  norm_num

end OAI
