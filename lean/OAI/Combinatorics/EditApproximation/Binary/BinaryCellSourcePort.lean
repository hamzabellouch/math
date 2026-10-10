import OAI.Combinatorics.EditApproximation.Binary.BinarySampledSourcePort
import OAI.Combinatorics.EditApproximation.Binary.BinaryCellReads

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

/-- The same raw dyadic scale list and Fin-count indices as the original
cell estimator, now with the cost of decoding every sampled coordinate. -/
def preparedCellGroupSourceWithWork (cell : ℕ × ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let centers := cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell
  let members := filterMapWithWork
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R C hr hi) centers.1
  if h : members.1 = [] then (none, centers.2 + members.2 + 1) else
    let selected := sampledGroupActionSourceWithWork source target parent b P exponent Q tau (nat F)
      (fun i q => (child i q).1) initial current (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) members.1 h
    (some selected.1, centers.2 + members.2 + selected.2 + 2)

theorem preparedCellGroupSourceWithWork_eq_cost (cell : ℕ × ℕ) (S : ℕ)
    (hs : ∀ t i, (draw t i).2 ≤ S) :
    (preparedCellGroupSourceWithWork source target parent b P F exponent Q hb hP tau a
      parentInitial child initial current R C hr hi raw hraw draw cell).1 =
      (preparedCellGroupReadWithWork source target parent b P F exponent Q hb hP tau a
        parentInitial child initial current R C hr hi raw hraw (fun t i => (draw t i).1) cell).1 ∧
    (preparedCellGroupSourceWithWork source target parent b P F exponent Q hb hP tau a
      parentInitial child initial current R C hr hi raw hraw draw cell).2 ≤
      (preparedCellGroupReadWithWork source target parent b P F exponent Q hb hP tau a
        parentInitial child initial current R C hr hi raw hraw (fun t i => (draw t i).1) cell).2 * (S + 4) := by
  let centers := cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell
  let members := filterMapWithWork
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R C hr hi) centers.1
  unfold preparedCellGroupSourceWithWork preparedCellGroupReadWithWork
  dsimp only
  split_ifs with hempty
  · exact ⟨rfl, by dsimp only; nlinarith only [Nat.zero_le S]⟩
  · have h := sampledGroupActionSourceWithWork_eq_cost source target parent b P exponent Q tau (nat F)
      (fun i q => (child i q).1) initial current (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) members.1 hempty S
      (fun t j => hs t _)
    dsimp only [dyadicSampledGroupActionReadWithWork]
    rw [h.1]
    exact ⟨rfl, by nlinarith only [h.2]⟩

theorem preparedCellGroupSourceWithWork_value (cell : ℕ × ℕ) :
    (preparedCellGroupSourceWithWork source target parent b P F exponent Q hb hP tau a
      parentInitial child initial current R C hr hi raw hraw draw cell).1 =
      (preparedCellGroupReadWithWork source target parent b P F exponent Q hb hP tau a
        parentInitial child initial current R C hr hi raw hraw (fun t i => (draw t i).1) cell).1 := by
  unfold preparedCellGroupSourceWithWork preparedCellGroupReadWithWork
  dsimp only
  split_ifs with hempty
  · rfl
  · apply congrArg some
    exact sampledGroupActionSourceWithWork_value source target parent b P exponent Q tau (nat F)
      (fun i q => (child i q).1) initial current (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) _ hempty

end Cell
end EditApproximation.BinaryFraction

end OAI
