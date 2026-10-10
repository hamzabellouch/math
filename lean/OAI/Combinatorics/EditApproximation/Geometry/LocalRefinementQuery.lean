import OAI.Combinatorics.EditApproximation.Refinement.PhysicalWarmupQuery
import OAI.Combinatorics.EditApproximation.Geometry.GatheredLocalStep
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalInputEncoding
import OAI.Combinatorics.EditApproximation.Geometry.OnlineEarlierDependence
import OAI.Combinatorics.EditApproximation.Geometry.EarlierValueDependence
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A local refinement query first reads its finite earlier-history
cover, then the shared current samples, and finally the selected actions.
The continuation is allowed to choose the last list from earlier answers. -/

namespace EditApproximation



theorem historyInputCode_injective (M n : ℕ) :
    Function.Injective (historyInputCode (M := M) (n := n)) := by
  rintro ⟨i, s, q⟩ ⟨i', s', q'⟩ heq
  have h := Nat.pair_eq_pair.mp heq
  have hc := childInputCode_injective M n h.2
  cases hc
  cases h.1
  rfl

section Step

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)



theorem localRefinementStepQuery_value (oracle : ι → ℚ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw integer q readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  let earlierCover := queryEarlierInputCover (M := M) parent N P F exponent t a parentInitial q
  let earlierKeys := orderedInputs historyInputCode (historyInputCode_injective M target.length) earlierCover
  let cachedEarlier := fun i s r => finiteAnswerTable earlierKeys
    (earlierKeys.map fun input => earlier input.1 input.2.1 input.2.2) (i, s, r)
  have hearlier : ∀ i s r, (i, s, r) ∈ earlierCover → cachedEarlier i s r = earlier i s r := by
    intro i s r hr
    exact finiteAnswerTable_map earlierKeys _ _
      ((mem_orderedInputs historyInputCode (historyInputCode_injective M target.length) earlierCover _).2 hr)
  have honline := localOnlineCandidates_congr_earlier_cover source target parent N P F exponent H t
    tau a eta kappa parentInitial child initial cachedEarlier earlier (t - 1) integer q (by omega) hearlier
  let online := localOnlineCandidates source target parent N P F exponent H tau a eta kappa
    parentInitial child initial earlier (t - 1) integer q
  let shared := querySharedInputCover source target parent N F exponent Q a parentInitial q draw
  let sharedKeys := orderedInputs childInputCode (childInputCode_injective M target.length) shared
  let sharedCurrent := fun i r => finiteAnswerTable sharedKeys
    (sharedKeys.map fun input => current input.1 input.2) (i, r)
  have hshared : ∀ input ∈ shared, sharedCurrent input.1 input.2 = current input.1 input.2 := by
    intro input hi
    exact finiteAnswerTable_map sharedKeys _ input
      ((mem_orderedInputs childInputCode (childInputCode_injective M target.length) shared input).2 hi)
  have hselected := localCellGroupActions_congr_cover source target parent N P F exponent Q tau a
    parentInitial child initial sharedCurrent current draw q hshared
  let selected := localCellGroupActions source target parent N P F exponent Q tau a
    parentInitial child initial current draw q
  let needed := actionCurrentInputCover selected ∪ actionCurrentInputCover online
  let currentKeys := orderedInputs childInputCode (childInputCode_injective M target.length) needed
  let cachedCurrent := finiteAnswerTable currentKeys (currentKeys.map fun input => current input.1 input.2)
  have hcurrent : ∀ input ∈ needed, cachedCurrent input = current input.1 input.2 := by
    intro input hi
    exact finiteAnswerTable_map currentKeys _ input
      ((mem_orderedInputs childInputCode (childInputCode_injective M target.length) needed input).2 hi)
  have hgroupValues := rationalActionValues_congr_cover
    (fun q r : TargetInterval target.length => (targetEndpointDistance q r : ℚ)) (128 * F) selected q
    cachedCurrent (fun input => current input.1 input.2)
    (fun input hi => hcurrent input (Finset.mem_union_left _ hi))
  have honlineValues := rationalActionValues_congr_cover
    (fun q r : TargetInterval target.length => (targetEndpointDistance q r : ℚ)) (128 * F) online q
    cachedCurrent (fun input => current input.1 input.2)
    (fun input hi => hcurrent input (Finset.mem_union_right _ hi))
  have hfallback := localBellman_congr_earlier parent N P F exponent t (t - 1) a parentInitial q
    cachedEarlier earlier (by omega) (fun input hi => hearlier input.1 input.2.1 input.2.2 hi) (128 * F)
  unfold localRefinementStepQuery
  rw [FiniteQuery.collect_value]
  simp only [hreadEarlier]
  change (FiniteQuery.collect readCurrent sharedKeys _).value oracle = _
  rw [FiniteQuery.collect_value]
  simp only [hreadCurrent]
  change (FiniteQuery.collect readCurrent
    (orderedInputs childInputCode (childInputCode_injective M target.length)
      (actionCurrentInputCover (localCellGroupActions source target parent N P F exponent Q tau a
        parentInitial child initial sharedCurrent draw q) ∪
        actionCurrentInputCover (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
          parentInitial child initial cachedEarlier (t - 1) integer q))) _).value oracle = _
  rw [hselected, honline, FiniteQuery.collect_value]
  simp only [hreadCurrent, FiniteQuery.value]
  change rationalRefinementUpdate delta
      (rationalMinimum _ (selected.map (rationalActionValue _ _ cachedCurrent q)))
      (rationalOnlineMinimum (online.map (rationalActionValue _ _ cachedCurrent q))) = _
  rw [hgroupValues, honlineValues, hfallback]
  rfl

end Step

end EditApproximation

end OAI
