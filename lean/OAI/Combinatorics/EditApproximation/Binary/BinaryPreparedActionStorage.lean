import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedLocalKernel
import OAI.Combinatorics.EditApproximation.Binary.BinaryWideActionsWork

namespace OAI

/-! Every emitted group/online action carries a bounded stored connection.
This is a property of the literal constructors on every draw, without a
successful-seed event or an assumed geometric bound. -/

namespace EditApproximation
namespace BinaryFraction

private theorem optionalBranch_property {A : Type*} (p : Prop) [Decidable p]
    (emptyCost : ℕ) (selected : ¬p → A × ℕ) (selectedCost : ¬p → ℕ)
    (property : A → Prop) (hselected : ∀ h, property (selected h).1) (action : A)
    (ha : (if h : p then (none, emptyCost) else
      (some (selected h).1, selectedCost h)).1 = some action) : property action := by
  by_cases h : p
  · have hnone : (none : Option A) = some action := by
      simpa only [dite_eq_left h] using ha
    cases hnone
  · have hsome : some (selected h).1 = some action := by
      simpa only [dite_eq_right h] using ha
    exact (Option.some.inj hsome) ▸ hselected h

private theorem filterMapWithWork_property {A C : Type*}
    (callback : C → Option A × ℕ) (inputs : List C) (property : A → Prop)
    (hcallback : ∀ input action, (callback input).1 = some action → property action)
    (action : A) (ha : action ∈ (filterMapWithWork callback inputs).1) : property action := by
  rw [filterMapWithWork_value] at ha
  obtain ⟨input, _, hsome⟩ := List.mem_filterMap.mp ha
  exact hcallback input action hsome

private theorem arithmeticFlatMapWithWork_property {A C : Type*}
    (callback : C → List A × ℕ) (inputs : List C) (property : A → Prop)
    (hcallback : ∀ input action, action ∈ (callback input).1 → property action)
    (action : A) (ha : action ∈ (arithmeticFlatMapWithWork callback inputs).1) : property action := by
  rw [arithmeticFlatMapWithWork_value] at ha
  obtain ⟨input, _, hmem⟩ := List.mem_flatMap.mp ha
  exact hcallback input action hmem

private theorem conditionalList_property {A : Type*} (p : Prop) [Decidable p]
    (selected : List A × ℕ) (selectedCost emptyCost : ℕ) (property : A → Prop)
    (hselected : ∀ action ∈ selected.1, property action) (action : A)
    (ha : action ∈ (if p then (selected.1, selectedCost) else ([], emptyCost)).1) :
    property action := by
  by_cases h : p
  · have hmem : action ∈ selected.1 := by simpa only [ite_eq_left h] using ha
    exact hselected action hmem
  · have hmem : action ∈ ([] : List A) := by simpa only [ite_eq_right h] using ha
    exact False.elim (List.not_mem_nil hmem)

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)
  (members : List (UnskippedBand source target parent b P exponent tau.value F.value
    (fun i q => (child i q).value) (fun i q => (initial i q).value))) (hne : members ≠ [])

theorem sampledGroupActionWithWork_connection (B : ℕ) (hn : Nat.size target.length + 2 ≤ B) :
    (sampledGroupActionWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1.connection.width ≤ connectionWordBudget M B := by
  unfold sampledGroupActionWithWork
  exact (endpointActionWithWork_bounds _ _ B hn).1

end Group

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
  (hP : 0 < P) (cell : ℕ × ℕ)

theorem preparedCellGroupWithWork_connection
    (action : BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M)
    (ha : (preparedCellGroupWithWork source target parent b P F exponent Q hb tau a parentInitial
      child initial current raw hraw draw hP cell).1 = some action)
    (B : ℕ) (hn : Nat.size target.length + 2 ≤ B) :
    action.connection.width ≤ connectionWordBudget M B := by
  let centers := cellCentersWithWork P F b a (inversePowerTwo exponent) parentInitial cell
  let members := filterMapWithWork
    (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F) child initial)
    centers.1
  let selected := fun hne : members.1 ≠ [] =>
    dyadicSampledGroupActionWithWork source target parent b P exponent Q tau (nat F)
      child initial current raw hraw draw members.1 hne
  have hconnection (hne : members.1 ≠ []) :
      (selected hne).1.connection.width ≤ connectionWordBudget M B := by
    have hh := sampledGroupActionWithWork_connection source target parent b P exponent Q tau (nat F)
      child initial current (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) members.1 hne B hn
    simpa only [selected, dyadicSampledGroupActionWithWork] using hh
  have habranch : (if h : members.1 = [] then (none, centers.2 + members.2 + 1) else
      (some (selected h).1, centers.2 + members.2 + (selected h).2 + 2)).1 = some action := by
    simpa only [preparedCellGroupWithWork, centers, members, selected] using ha
  exact optionalBranch_property (members.1 = []) (centers.2 + members.2 + 1) selected
    (fun hne => centers.2 + members.2 + (selected hne).2 + 2)
    (fun action => action.connection.width ≤ connectionWordBudget M B) hconnection action habranch

end Cell

theorem preparedComputedCellGroupWithWork_connection {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hb : b = 2 ^ eb) (hF : F = 2 ^ eF) (hP : 0 < P)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ)
    (action : BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M)
    (ha : (preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF
      hM hb hF hP tau a parentInitial child initial current draw cell).1 = some action)
    (B : ℕ) (hn : Nat.size target.length + 2 ≤ B) :
    action.connection.width ≤ connectionWordBudget M B := by
  have hcell : (preparedCellGroupWithWork source target parent b P F exponent Q
      (by rw [hb]; exact Nat.two_pow_pos eb) tau a parentInitial child initial current
      (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF)
      draw hP cell).1 = some action := by
    simpa only [preparedComputedCellGroupWithWork] using ha
  exact preparedCellGroupWithWork_connection source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) tau a parentInitial child initial current
    (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF)
    draw hP cell action hcell B hn

theorem preparedLocalGroupScaleWithWork_connection {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent Q eM eF eb : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (B : ℕ) (hn : Nat.size target.length + 2 ≤ B)
    (action : BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M)
    (ha : action ∈ (preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb
      hM hF hP tau a parentInitial child initial current draw query).1) :
    action.connection.width ≤ connectionWordBudget M B := by
  let cellDraw := fun cell : ℕ × ℕ =>
    Eq.mpr (congrArg (cellScaleDraw M (2 ^ eb) Q) (nat_value F)) (draw (2 ^ eb) cell)
  let callback := fun cell : ℕ × ℕ =>
    preparedComputedCellGroupWithWork source target parent (2 ^ eb) P F exponent Q eM eb eF
      hM rfl hF hP tau a parentInitial child initial current (cellDraw cell) cell
  let cells := (targetCellsWithWork
    (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
    (bitWordValue (naturalCeilingWithWork (parentInitial query)).1) query).1
  have hcallback (cell : ℕ × ℕ)
      (result : BinaryBellmanAction (TargetInterval target.length)
        (Fin M × TargetInterval target.length) M)
      (hresult : (callback cell).1 = some result) :
      result.connection.width ≤ connectionWordBudget M B := by
    have hcell : (preparedComputedCellGroupWithWork source target parent (2 ^ eb) P F exponent Q eM eb eF
        hM rfl hF hP tau a parentInitial child initial current (cellDraw cell) cell).1 = some result := by
      simpa only [callback] using hresult
    have hh := preparedComputedCellGroupWithWork_connection source target parent (2 ^ eb) P F exponent Q eM eb eF
      hM rfl hF hP tau a parentInitial child initial current (cellDraw cell) cell result hcell B hn
    exact hh
  have hfiltered : action ∈ (filterMapWithWork callback cells).1 := by
    simpa only [preparedLocalGroupScaleWithWork, callback, cells, cellDraw] using ha
  exact filterMapWithWork_property callback cells
    (fun result => result.connection.width ≤ connectionWordBudget M B) hcallback action hfiltered

theorem preparedLocalCellGroupsWithWork_connection {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (B : ℕ) (hn : Nat.size target.length + 2 ≤ B)
    (action : BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M)
    (ha : action ∈ (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current draw query).1) :
    action.connection.width ≤ connectionWordBudget M B := by
  let callback := fun eb : ℕ =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query)
    if guard.1 then
      let selected := preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb
        hM hF hP tau a parentInitial child initial current draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)
  have hcallback (eb : ℕ)
      (result : BinaryBellmanAction (TargetInterval target.length)
        (Fin M × TargetInterval target.length) M)
      (hresult : result ∈ (callback eb).1) :
      result.connection.width ≤ connectionWordBudget M B := by
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query)
    let selected := preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb
      hM hF hP tau a parentInitial child initial current draw query
    have hguarded : result ∈ (if guard.1 = true then
        (selected.1, guard.2 + selected.2 + eb + 4) else ([], guard.2 + eb + 4)).1 := by
      simpa only [callback, guard, selected] using hresult
    exact conditionalList_property (guard.1 = true) selected
      (guard.2 + selected.2 + eb + 4) (guard.2 + eb + 4)
      (fun result => result.connection.width ≤ connectionWordBudget M B)
      (fun result hmem => preparedLocalGroupScaleWithWork_connection source target parent P F exponent Q
        eM eF eb hM hF hP tau a parentInitial child initial current draw query B hn result hmem)
      result hguarded
  have hflat : action ∈ (arithmeticFlatMapWithWork callback (List.range (max 1 N.bits.length))).1 := by
    simpa only [preparedLocalCellGroupsWithWork, callback] using ha
  exact arithmeticFlatMapWithWork_property callback (List.range (max 1 N.bits.length))
    (fun result => result.connection.width ≤ connectionWordBudget M B) hcallback action hflat

theorem preparedOnlineWithWork_connection {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ)
    (action : BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M)
    (ha : (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa child initial
      table t center integer).1 = some action) : action.connection = zero := by
  unfold preparedOnlineWithWork at ha
  dsimp only at ha
  split_ifs at ha with hempty hactive
  cases ha
  rfl

theorem preparedLocalOnlineActionsWithWork_connection {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (hP : 0 < P)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length)
    (action : BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M)
    (ha : action ∈ (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a
      eta kappa parentInitial child initial table t integer query).1) : action.connection = zero := by
  simp only [preparedLocalOnlineActionsWithWork, filterMapWithWork_value] at ha
  obtain ⟨eb, _, hmem⟩ := List.mem_filterMap.mp ha
  unfold preparedLocalOnlineScaleWithWork at hmem
  dsimp only at hmem
  split_ifs at hmem with heligible
  exact preparedOnlineWithWork_connection source target parent P F exponent H (2 ^ eb)
    (Nat.two_pow_pos _) hP tau eta kappa child initial table t _ _ action hmem

end BinaryFraction
end EditApproximation

end OAI
