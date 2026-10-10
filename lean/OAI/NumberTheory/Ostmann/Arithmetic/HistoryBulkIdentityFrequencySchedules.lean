import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIdentityFrequencyBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealizationMetadata

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIdentityFrequency
open Construction Characters.FrequencyExposure HistoryFrequencyResidues

private theorem map_reverseAddressSchedule {α β : Type*} (f : α → β)
    (root : α) (left right : List Bool → α) :
    (fun p => f (reverseAddressSchedule root left right p)) =
      reverseAddressSchedule (f root) (fun p => f (left p)) (fun p => f (right p)) := by
  funext p
  unfold reverseAddressSchedule
  split <;> rfl

theorem leftData_frequencyScheduleAux (R : ℕ) {l : ℕ} (h k : History l)
    (hF : ∀ s ∈ h.frequencies, s.natAbs ∣ R)
    (kF : ∀ s ∈ k.frequencies, s.natAbs ∣ R) :
    (fun p => leftData (frequencyScheduleAux R h k hF kF p)) =
      frequencyScheduleAux R h h hF hF := by
  induction h with
  | leaf a => cases k; rfl
  | node a pivot u hp hm left right ihl ihr =>
    cases k with
    | node a' pivot' u' hp' hm' left' right' =>
      simp only [frequencyScheduleAux]
      rw [map_reverseAddressSchedule, ihl, ihr]
      rfl

theorem rightData_frequencyScheduleAux (R : ℕ) {l : ℕ} (h k : History l)
    (hF : ∀ s ∈ h.frequencies, s.natAbs ∣ R)
    (kF : ∀ s ∈ k.frequencies, s.natAbs ∣ R) :
    (fun p => rightData (frequencyScheduleAux R h k hF kF p)) =
      frequencyScheduleAux R k k kF kF := by
  induction h with
  | leaf a => cases k; rfl
  | node a pivot u hp hm left right ihl ihr =>
    cases k with
    | node a' pivot' u' hp' hm' left' right' =>
      simp only [frequencyScheduleAux]
      rw [map_reverseAddressSchedule, ihl, ihr]
      rfl

theorem leftFactors_fixedFactorSchedule {l : ℕ} (h k : History l) :
    (fun p => leftFactors (fixedFactorSchedule h k p)) = fixedFactorSchedule h h := by
  induction h with
  | leaf a => cases k; rfl
  | node a pivot u hp hm left right ihl ihr =>
    cases k with
    | node a' pivot' u' hp' hm' left' right' =>
      simp only [fixedFactorSchedule]
      rw [map_reverseAddressSchedule, ihl, ihr]
      rfl

theorem rightFactors_fixedFactorSchedule {l : ℕ} (h k : History l) :
    (fun p => rightFactors (fixedFactorSchedule h k p)) = fixedFactorSchedule k k := by
  induction h with
  | leaf a => cases k; rfl
  | node a pivot u hp hm left right ihl ihr =>
    cases k with
    | node a' pivot' u' hp' hm' left' right' =>
      simp only [fixedFactorSchedule]
      rw [map_reverseAddressSchedule, ihl, ihr]
      rfl

end Ostmann.Arithmetic.HistoryBulkIdentityFrequency

end

end OAI
