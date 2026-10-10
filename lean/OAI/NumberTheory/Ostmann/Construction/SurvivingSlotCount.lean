import OAI.NumberTheory.Ostmann.Construction.ScheduledTemplateBounds
import OAI.NumberTheory.Ostmann.Construction.ScheduledBulkMatchingCount

namespace OAI

/-! # Sharp slot counts after erasing each pivot

Only surviving positions matter. Each position is either doubled or retained,
so the growth factor is two even though the ambient label type grows by three.
-/

namespace Ostmann
open scoped Classical

theorem copyScheduleAtoms_succ_card {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) :
    Fintype.card (CopyScheduleAtoms role (n + 1)) =
      2 * Fintype.card (CopyScheduleH role n) + Fintype.card (CopyScheduleY role n) := by
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool] using
    Fintype.card_congr (copyScheduleSurvivorEquiv role n)

theorem copyScheduleAtoms_partition_card {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) :
    Fintype.card (CopyScheduleAtoms role n) =
      Fintype.card (CurrentPivotConstituent role n) +
        (Fintype.card (CopyScheduleH role n) + Fintype.card (CopyScheduleY role n)) := by
  simpa only [Fintype.card_sum] using (Fintype.card_congr (scheduledPartitionEquiv role n)).symm

theorem copyScheduleAtoms_card_sharp {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) :
    Fintype.card (CopyScheduleAtoms role n) ≤ 2 ^ n * Fintype.card I := by
  induction n with
  | zero => simp only [copyScheduleAtoms_zero_card, pow_zero, one_mul, le_refl]
  | succ n ih =>
    have hp := copyScheduleAtoms_partition_card role n
    rw [copyScheduleAtoms_succ_card, pow_succ]
    calc
      _ ≤ 2 * (2 ^ n * Fintype.card I) := by omega
      _ = _ := by ring

theorem copyScheduleH_card_sharp {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) :
    Fintype.card (CopyScheduleH role n) ≤ 2 ^ n * Fintype.card I := by
  have h := copyScheduleAtoms_partition_card role n
  exact (show Fintype.card (CopyScheduleH role n) ≤
    Fintype.card (CopyScheduleAtoms role n) by omega).trans (copyScheduleAtoms_card_sharp role n)

theorem scheduledNonbulkH_card_sharp {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) :
    Fintype.card (ScheduledNonbulkH role n) ≤
      2 ^ n * Fintype.card {i : I // role i ≠ .word} := by
  have hsplit : 2 ^ n * m + Fintype.card (ScheduledNonbulkH role n) =
      Fintype.card (CopyScheduleH role n) := by
    simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using
      Fintype.card_congr (scheduledSplitHCoordinates role n m word)
  have hword : Fintype.card {i : I // role i = .word} = m := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr word).symm
  have hcard : Fintype.card I = m + Fintype.card {i : I // role i ≠ .word} := by
    have he := Fintype.card_subtype_compl (fun i : I => role i = .word)
    have hle := Fintype.card_subtype_le (fun i : I => role i = .word)
    rw [hword] at he hle
    have he' : Fintype.card {i : I // role i ≠ .word} = Fintype.card I - m := by
      simpa only [ne_eq] using he
    rw [he']
    omega
  have hb := copyScheduleH_card_sharp role n
  rw [hcard, Nat.mul_add] at hb
  omega

end Ostmann

end OAI
