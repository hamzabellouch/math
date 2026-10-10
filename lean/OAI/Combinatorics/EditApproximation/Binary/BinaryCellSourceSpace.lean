import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupActionSourceSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryCellSourcePort
import OAI.Combinatorics.EditApproximation.Binary.BinaryUnskippedSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalRepresentativeSpace

namespace OAI

namespace EditApproximation.BinaryFraction

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R C : ℕ) (hr : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M × ℕ)
  (parentAllocation : TargetInterval target.length → ℕ)
  (childAllocation initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)
  (drawAllocation : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → ℕ)

def preparedCellGroupSourceAllocation (cell : ℕ × ℕ) : ℕ :=
  let centers := (cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell).1
  let members := (filterMapWithWork
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R C hr hi) centers).1
  cellCentersReadAllocation P F b a (inversePowerTwo exponent) parentInitial parentAllocation cell +
    filterMapAllocation (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R C hr hi)
      (fun center => preparedUnskippedReadAllocation parent center b P exponent tau (nat F)
        child initial childAllocation initialAllocation) centers +
    if hempty : members = [] then 0 else
      sampledGroupActionSourceAllocation source target parent b P exponent Q tau (nat F)
        (fun i q => (child i q).1) initial current initialAllocation currentAllocation
        (indexedGroupScales raw M b (nat F).value hraw)
        (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
          (indexedGroupScales_value raw M b (nat F).value hraw t)) j))
        (fun t j => drawAllocation t (Fin.cast (congrArg (groupSampleCount M Q b)
          (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) members hempty + 1

theorem preparedCellGroupSourceAllocation_le_work (cell : ℕ × ℕ)
    (hp : ∀ q, parentAllocation q ≤ (parentInitial q).2)
    (hc : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hin : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hcur : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (hd : ∀ t i, drawAllocation t i ≤ (draw t i).2) :
    preparedCellGroupSourceAllocation source target parent b P F exponent Q hb hP tau a
      parentInitial child initial current R C hr hi raw hraw draw
      parentAllocation childAllocation initialAllocation currentAllocation drawAllocation cell ≤
      (preparedCellGroupSourceWithWork source target parent b P F exponent Q hb hP tau a
        parentInitial child initial current R C hr hi raw hraw draw cell).2 := by
  let centers := (cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell).1
  let members := (filterMapWithWork
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R C hr hi) centers).1
  have hcenters := cellCentersReadAllocation_le_work P F b a (inversePowerTwo exponent)
    parentInitial parentAllocation cell hp
  have hmembers := filterMapAllocation_le_work
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R C hr hi)
    (fun center => preparedUnskippedReadAllocation parent center b P exponent tau (nat F)
      child initial childAllocation initialAllocation) centers
    (fun center _ => preparedUnskippedReadAllocation_le_work source target parent center b P exponent
      hb hP tau (nat F) child initial childAllocation initialAllocation R C hr hi hc hin)
  dsimp only [centers] at hmembers
  unfold preparedCellGroupSourceAllocation preparedCellGroupSourceWithWork
  dsimp only
  split_ifs with hempty
  · exact Nat.add_le_add (Nat.add_le_add hcenters hmembers) (by decide : 0 ≤ 1)
  · have hsample := sampledGroupActionSourceAllocation_le_work source target parent b P exponent Q
      tau (nat F) (fun i q => (child i q).1) initial current initialAllocation currentAllocation
      (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j))
      (fun t j => drawAllocation t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) members hempty hin hcur
      (fun t j => hd t _)
    dsimp only [centers, members] at hmembers hsample
    exact (Nat.add_assoc _ _ _).symm.le.trans
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hcenters hmembers) hsample)
        (by decide : 1 ≤ 2))

end Cell
end EditApproximation.BinaryFraction

end OAI
