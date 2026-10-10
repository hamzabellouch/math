import OAI.Combinatorics.EditApproximation.Binary.BinaryCellCenters
import OAI.Combinatorics.EditApproximation.Binary.BinaryDyadicSampledGroups
import OAI.Combinatorics.EditApproximation.Binary.BinaryUnskippedKernel

namespace OAI

/-! One complete whole-cell group: enumerate its eligible centers, execute
every band guard, estimate all surviving members with the original finite
draws, and select the same ordered minimum. -/

namespace EditApproximation
namespace BinaryFraction

abbrev cellScaleDraw (M b Q : ℕ) (f : ℚ) :=
  ∀ t : Fin (groupDyadicScales M b f).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b f t)) → Fin M

def cellReferenceAction {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (tau a f : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (cell : ℕ × ℕ) (draw : cellScaleDraw M b Q f) : Option (PhysicalRationalAction M target.length) :=
  let members := unskippedBandList source target parent b P exponent tau f child initial
    (cellRepresentativeStates target.length P F b a parentInitial ((2 : ℚ) ^ (-(exponent : ℤ))) cell)
  if h : members = [] then none else some (chooseUnskippedGroup Q current members h draw).rationalAction

theorem cellReferenceAction_transport {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (tau a f g : ℚ) (h : f = g)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (cell : ℕ × ℕ) (draw : cellScaleDraw M b Q f) :
    cellReferenceAction source target parent b P F exponent Q tau a f parentInitial child initial current cell draw =
      cellReferenceAction source target parent b P F exponent Q tau a g parentInitial child initial current cell
        (Eq.mp (congrArg (cellScaleDraw M b Q) h) draw) := by
  cases h
  rfl

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (raw : List BinaryFraction)
  (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M)

def cellGroupWithWork (cell : ℕ × ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let centers := cellCentersWithWork P F b a (inversePowerTwo exponent) parentInitial cell
  let members := filterMapWithWork
    (unskippedCandidateWithWork source target parent b P exponent hb tau (nat F) child initial) centers.1
  if h : members.1 = [] then (none, centers.2 + members.2 + 1) else
    let selected := dyadicSampledGroupActionWithWork source target parent b P exponent Q tau (nat F)
      child initial current raw hraw draw members.1 h
    (some selected.1, centers.2 + members.2 + selected.2 + 2)

theorem cellGroupWithWork_reference (cell : ℕ × ℕ) (hP : 0 < P) :
    ((cellGroupWithWork source target parent b P F exponent Q hb tau a parentInitial child initial current
      raw hraw draw cell).1.map BinaryBellmanAction.decode) =
      cellReferenceAction source target parent b P F exponent Q tau.value a.value (nat F).value
        (fun q => (parentInitial q).value) (fun i q => (child i q).value)
        (fun i q => (initial i q).value) (fun i q => (current i q).value) cell draw := by
  have hcenters := cellCentersWithWork_value P F b a (inversePowerTwo exponent) parentInitial cell hP
  simp only [inversePowerTwo_value] at hcenters
  have hmembers : (filterMapWithWork
      (unskippedCandidateWithWork source target parent b P exponent hb tau (nat F) child initial)
      (cellCentersWithWork P F b a (inversePowerTwo exponent) parentInitial cell).1).1 =
      unskippedBandList source target parent b P exponent tau.value (nat F).value
        (fun i q => (child i q).value) (fun i q => (initial i q).value)
        (cellRepresentativeStates target.length P F b a.value
          (fun q => (parentInitial q).value) ((2 : ℚ) ^ (-(exponent : ℤ))) cell) := by
    simp only [filterMapWithWork_value, unskippedCandidateWithWork_value, hcenters, unskippedBandList]
  unfold cellGroupWithWork
  dsimp only
  split_ifs with hempty
  · have hnil := hempty
    rw [hmembers] at hnil
    simp only [Option.map_none, cellReferenceAction, dite_eq_left hnil]
  · rw [Option.map_some, dyadicSampledGroupActionWithWork_value source target parent b P exponent Q
      tau (nat F) child initial current raw hraw draw _ hempty hb]
    have hnonempty := hempty
    rw [hmembers] at hnonempty
    simp only [hmembers, cellReferenceAction, dite_eq_right hnonempty]

/-- The rational cell-group program at the exact natural parameter.
Transport preserves its values and changes only proof indices. -/
theorem cellGroupWithWork_value (cell : ℕ × ℕ) (hP : 0 < P) :
    ((cellGroupWithWork source target parent b P F exponent Q hb tau a parentInitial child initial current
      raw hraw draw cell).1.map BinaryBellmanAction.decode) =
      chooseCellGroupAction source target parent b P F exponent Q tau.value a.value
        (fun q => (parentInitial q).value) (fun i q => (child i q).value)
        (fun i q => (initial i q).value) (fun i q => (current i q).value) cell
        (Eq.mp (congrArg (cellScaleDraw M b Q) (nat_value F)) draw) := by
  exact (cellGroupWithWork_reference source target parent b P F exponent Q hb tau a parentInitial
    child initial current raw hraw draw cell hP).trans
      (cellReferenceAction_transport source target parent b P F exponent Q tau.value a.value _ _
        (nat_value F) _ _ _ _ cell draw)

end Cell
end BinaryFraction
end EditApproximation

end OAI
