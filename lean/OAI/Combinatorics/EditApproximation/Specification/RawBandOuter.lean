import OAI.Combinatorics.EditApproximation.Specification.RawBandConsumers
import OAI.Combinatorics.EditApproximation.Definitions

namespace OAI.EditApproximation.BinaryFraction

def dyadicSampledGroupActionReadWithWorkRaw {ny M : ℕ}
    (b exponent Q : ℕ) (F : BinaryFraction)
    (initial current : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b F.value)
    (draw : ∀ t : Fin (groupDyadicScales M b F.value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F.value t)) → Fin M)
    (members : List (RawUnskippedBand M ny)) (hne : members ≠ []) :=
  sampledGroupActionReadWithWorkRaw b exponent Q initial current
    (indexedGroupScales raw M b F.value hraw)
    (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
      (indexedGroupScales_value raw M b F.value hraw t)) j)) members hne

def preparedCellGroupReadWithWorkRaw {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (_hb : 0 < b) (_hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R C : ℕ) (_hr : ∀ i q, (child i q).2 ≤ R) (_hi : ∀ i q, (initial i q).2 ≤ C)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M)


    (cell : ℕ × ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let centers := cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell
  let members := filterMapWithWork
    (preparedUnskippedReadWithWorkRaw parent b P exponent tau (nat F) child initial) centers.1
  if h : members.1 = [] then (none, centers.2 + members.2 + 1) else
    let selected := dyadicSampledGroupActionReadWithWorkRaw b exponent Q (nat F) initial current raw hraw draw members.1 h
    (some selected.1, centers.2 + members.2 + selected.2 + 2)









end OAI.EditApproximation.BinaryFraction
