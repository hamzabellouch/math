import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupReadCosts
import OAI.Combinatorics.EditApproximation.Binary.BinaryCellReads

namespace OAI

/-! The complete whole-cell estimator, including its ordered choice,
executes with a linear factor for each finite-buffer lookup. -/

namespace EditApproximation
namespace BinaryFraction

theorem cellCentersReadWithWork_factor {n : ℕ} (P F b : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction × ℕ) (cell : ℕ × ℕ)
    (R : ℕ) (hr : ∀ r, (initial r).2 ≤ R) :
    (cellCentersReadWithWork P F b a theta initial cell).2 ≤
      (cellCentersWithWork P F b a theta (fun r => (initial r).1) cell).2 * tableReadFactor R := by
  have h := (cellCentersReadWithWork_eq_cost P F b a theta initial cell R hr).2
  have hK : R + 1 ≤ tableReadFactor R := by unfold tableReadFactor; omega
  exact h.trans (Nat.mul_le_mul_left _ hK)

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M)

theorem preparedCellGroupReadWithWork_factor (cell : ℕ × ℕ)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (hn : ∀ i q, (current i q).2 ≤ R) :
    (preparedCellGroupReadWithWork source target parent b P F exponent Q hb hP tau a
      parentInitial child initial current R R hc hi raw hraw draw cell).2 ≤
      (preparedCellGroupWithWork source target parent b P F exponent Q hb tau a
        (fun r => (parentInitial r).1) (fun i q => (child i q).1)
        (fun i q => (initial i q).1) (fun i q => (current i q).1) raw hraw draw hP cell).2 *
        tableReadFactor R := by
  have hcenters := cellCentersReadWithWork_factor P F b a (inversePowerTwo exponent)
    parentInitial cell R hp
  have hcentersq := (cellCentersReadWithWork_eq_cost P F b a (inversePowerTwo exponent)
    parentInitial cell R hp).1
  have hm := filterMapWithWork_factor
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R R hc hi)
    (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
      (fun i q => (child i q).1) (fun i q => (initial i q).1))
    (cellCentersWithWork P F b a (inversePowerTwo exponent) (fun r => (parentInitial r).1) cell).1
    (tableReadFactor R) (tableReadFactor_pos R)
    (fun center _ => preparedUnskippedReadWithWork_value source target parent b P exponent hb hP
      tau (nat F) child initial R R hc hi center)
    (fun center _ => preparedUnskippedReadWithWork_factor source target parent b P exponent hb hP
      tau (nat F) child initial R hc hi center)
  have hcm := Nat.add_le_add hcenters hm.2
  rw [← Nat.add_mul] at hcm
  unfold preparedCellGroupReadWithWork preparedCellGroupWithWork
  dsimp only
  simp only [hcentersq, hm.1]
  split_ifs with hempty
  · apply cost_replace_factor _ _ _ _ _ hcm (tableReadFactor_pos R) <;> omega
  · have hs := sampledGroupActionReadWithWork_factor source target parent b P exponent Q tau
      (nat F) (fun i q => (child i q).1) initial current
      (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j))
      _ hempty R hi hn
    have h := Nat.add_le_add hcm hs
    rw [← Nat.add_mul] at h
    change _ ≤ _ at hs
    unfold dyadicSampledGroupActionReadWithWork dyadicSampledGroupActionWithWork
    dsimp only
    apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

end Cell
end BinaryFraction
end EditApproximation

end OAI
