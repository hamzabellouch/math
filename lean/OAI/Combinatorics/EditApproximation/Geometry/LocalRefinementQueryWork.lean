import OAI.Combinatorics.EditApproximation.Geometry.LocalRefinementQuery
import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryWork

namespace OAI

/-! The literal three-stage query plan has the earlier-cover cost plus
at most twice the current-cover cost. This counts its executed readers,
including overlap between its two current gathers. -/

namespace EditApproximation

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
  (oracle : ι → ℚ) (weight : ι → ℕ)
  (earlier : PhysicalChildTables M target.length)
  (current : Fin M → TargetInterval target.length → ℚ)
  (ht : 0 < t)
  (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
  (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2)

include ht hreadEarlier hreadCurrent

theorem localRefinementStepQuery_cost :
    (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw integer q readEarlier readCurrent).cost oracle weight =
    ((orderedInputs historyInputCode (historyInputCode_injective M target.length)
      (queryEarlierInputCover parent N P F exponent t a parentInitial q)).map
        (fun input => (readEarlier input).cost oracle weight)).sum +
    ((orderedInputs childInputCode (childInputCode_injective M target.length)
      (querySharedInputCover source target parent N F exponent Q a parentInitial q draw)).map
        (fun input => (readCurrent input).cost oracle weight)).sum +
    ((orderedInputs childInputCode (childInputCode_injective M target.length)
      (actionCurrentInputCover
        (localCellGroupActions source target parent N P F exponent Q tau a
          parentInitial child initial current draw q) ∪
        actionCurrentInputCover
          (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
            parentInitial child initial earlier (t - 1) integer q))).map
        (fun input => (readCurrent input).cost oracle weight)).sum := by
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
  unfold localRefinementStepQuery
  rw [FiniteQuery.cost_collect]
  simp only [hreadEarlier]
  change _ + (FiniteQuery.collect readCurrent sharedKeys _).cost oracle weight = _
  rw [FiniteQuery.cost_collect]
  simp only [hreadCurrent]
  change _ + (_ + (FiniteQuery.collect readCurrent
    (orderedInputs childInputCode (childInputCode_injective M target.length)
      (actionCurrentInputCover (localCellGroupActions source target parent N P F exponent Q tau a
        parentInitial child initial sharedCurrent draw q) ∪
        actionCurrentInputCover (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
          parentInitial child initial cachedEarlier (t - 1) integer q))) _).cost oracle weight) = _
  rw [hselected, honline, FiniteQuery.cost_collect]
  simp only [FiniteQuery.cost, Nat.add_zero, Nat.add_assoc]
  rfl

theorem localRefinementStepQuery_cost_le (earlierCost currentCost : ℕ)
    (hcostEarlier : ∀ input, (readEarlier input).cost oracle weight ≤ earlierCost)
    (hcostCurrent : ∀ input, (readCurrent input).cost oracle weight ≤ currentCost) :
    (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw integer q readEarlier readCurrent).cost oracle weight ≤
    (queryEarlierInputCover (M := M) parent N P F exponent t a parentInitial q).card * earlierCost +
      2 * (currentQueryInputCover source target parent N P F exponent Q tau a parentInitial
        child initial current draw q
        (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
          parentInitial child initial earlier (t - 1) integer q)).card * currentCost := by
  rw [localRefinementStepQuery_cost source target parent N P F exponent H Q tau a eta kappa delta t
    parentInitial child initial draw integer q readEarlier readCurrent oracle weight earlier current
    ht hreadEarlier hreadCurrent]
  let online := localOnlineCandidates source target parent N P F exponent H tau a eta kappa
    parentInitial child initial earlier (t - 1) integer q
  let groups := localCellGroupActions source target parent N P F exponent Q tau a
    parentInitial child initial current draw q
  let shared := querySharedInputCover source target parent N F exponent Q a parentInitial q draw
  let needed := actionCurrentInputCover groups ∪ actionCurrentInputCover online
  let cover := currentQueryInputCover source target parent N P F exponent Q tau a parentInitial
    child initial current draw q online
  have hshared : shared.card ≤ cover.card := Finset.card_le_card (by
    intro input hi
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hi))
  have hneeded : needed.card ≤ cover.card := Finset.card_le_card (by
    intro input hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
    · exact Finset.mem_union_right _ hi)
  have bound {β : Type} [DecidableEq β] (code : β → ℕ) (hinj : Function.Injective code)
      (inputs : Finset β) (cost : β → ℕ) (B : ℕ) (hcost : ∀ x, cost x ≤ B) :
      ((orderedInputs code hinj inputs).map cost).sum ≤ inputs.card * B := by
    calc
      _ ≤ ((orderedInputs code hinj inputs).map (fun _ => B)).sum :=
        List.sum_le_sum (fun x _ => hcost x)
      _ = inputs.card * B := by simp only [List.map_const', List.sum_replicate,
        smul_eq_mul, orderedInputs_length]
  have he := bound (β := Fin M × ℕ × TargetInterval target.length)
    historyInputCode (historyInputCode_injective M target.length)
    (queryEarlierInputCover (M := M) parent N P F exponent t a parentInitial q)
    (fun input => (readEarlier input).cost oracle weight) earlierCost hcostEarlier
  have hs := bound childInputCode (childInputCode_injective M target.length) shared
    (fun input => (readCurrent input).cost oracle weight) currentCost hcostCurrent
  have hn := bound childInputCode (childInputCode_injective M target.length) needed
    (fun input => (readCurrent input).cost oracle weight) currentCost hcostCurrent
  have hs' := Nat.mul_le_mul_right currentCost hshared
  have hn' := Nat.mul_le_mul_right currentCost hneeded
  change _ ≤ _ + 2 * cover.card * currentCost
  nlinarith only [he, hs, hn, hs', hn']

end Step

end EditApproximation

end OAI
