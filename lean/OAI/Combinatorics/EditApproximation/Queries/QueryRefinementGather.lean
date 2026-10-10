import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryInputs
import OAI.Combinatorics.EditApproximation.Queries.QuerySharedInputs
import OAI.Combinatorics.EditApproximation.Queries.QueryActionInputs
import OAI.Combinatorics.EditApproximation.Binary.BitQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The last three adaptive gathers of a refinement request. Each request
list is constructed after the answers on which it depends. The selected
actions, list construction, sorting and buffer cells all carry work. -/

namespace EditApproximation

section Gather
variable {ι β α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (a : BinaryFraction) (t : ℕ)
  (initial : TargetInterval target.length → BinaryFraction × ℕ)
  (draw : CountedCellGroupDraws M F Q) (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (online : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ)
  (selected : List (Fin M × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ)
  (next : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (Fin M × TargetInterval target.length) → List BinaryFraction → BitQuery ι β)




theorem queryRefinementGather_work (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    let earlier := BinaryFraction.queryEarlierInputsWithWork M parent N P F exponent t hP a initial q
    let earlierWords := earlier.1.map fun key => (readEarlier key).value oracle
    let actions := online earlier.1 earlierWords
    let shared := BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF
      parent a (initial q).1 q draw
    let sharedWords := shared.1.map fun key => (readCurrent key).value oracle
    let groups := selected shared.1 sharedWords
    let current := queryNeededInputsWithWork groups.1 actions.1
    let currentWords := current.1.map fun key => (readCurrent key).value oracle
    (queryRefinementGather source target parent N P F exponent Q eM eF hP hM hF
      a t initial draw q readEarlier readCurrent online selected next).work oracle readWork =
      earlier.2 + (earlier.1.map fun key => (readEarlier key).work oracle readWork + 3).sum +
      actions.2 + (initial q).2 + shared.2 +
      (shared.1.map fun key => (readCurrent key).work oracle readWork + 3).sum +
      groups.2 + current.2 +
      (current.1.map fun key => (readCurrent key).work oracle readWork + 3).sum +
      (next earlier.1 earlierWords groups.1 actions.1 current.1 currentWords).work oracle readWork := by
  simp only [queryRefinementGather, BitQuery.work_bind, BitQuery.compute,
    BitQuery.work, BitQuery.value, BitQuery.work_collect,
    Nat.add_zero, Nat.add_assoc]

end Gather

section Simulation
variable {ι β α : Type*} {relation : β → ℚ → Prop}
  (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (a : BinaryFraction) (t : ℕ)
  (initial : TargetInterval target.length → BinaryFraction × ℕ)
  (draw : CountedCellGroupDraws M F Q) (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (expectedEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (expectedCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (online : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ)
  (selected : List (Fin M × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ)
  (expectedOnline : List (Fin M × ℕ × TargetInterval target.length) → List ℚ →
    List (RationalBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M))
  (expectedSelected : List (Fin M × TargetInterval target.length) → List ℚ →
    List (RationalBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M))
  (next : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (Fin M × TargetInterval target.length) → List BinaryFraction → BitQuery ι β)
  (expectedNext : List (Fin M × ℕ × TargetInterval target.length) → List ℚ →
    List (RationalBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (RationalBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (Fin M × TargetInterval target.length) → List ℚ → FiniteQuery ι)

theorem queryRefinementGather_refines
    (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R)
    (he : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readEarlier key) (expectedEarlier key))
    (hc : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readCurrent key) (expectedCurrent key))
    (ho : ∀ keys words, ((online keys words).1.map BinaryBellmanAction.decode) =
      expectedOnline keys (words.map BinaryFraction.value))
    (hs : ∀ keys words, ((selected keys words).1.map BinaryBellmanAction.decode) =
      expectedSelected keys (words.map BinaryFraction.value))
    (hn : ∀ earlierKeys earlierWords groups actions keys words,
      BitQuery.Refines relation (next earlierKeys earlierWords groups actions keys words)
        (expectedNext earlierKeys (earlierWords.map BinaryFraction.value)
          (groups.map BinaryBellmanAction.decode) (actions.map BinaryBellmanAction.decode)
          keys (words.map BinaryFraction.value))) :
    BitQuery.Refines relation
      (queryRefinementGather source target parent N P F exponent Q eM eF hP hM hF
        a t initial draw q readEarlier readCurrent online selected next)
      (let earlierKeys := orderedInputs historyInputCode (historyInputCode_injective M target.length)
          (queryEarlierInputCover parent N P F exponent t a.value (fun r => (initial r).1.value) q)
       FiniteQuery.collect expectedEarlier earlierKeys fun earlierWords =>
         let actions := expectedOnline earlierKeys earlierWords
         let sharedKeys := orderedInputs childInputCode (childInputCode_injective M target.length)
           (querySharedInputCover source target parent N F exponent Q a.value
             (fun r => (initial r).1.value) q (fun b cell scale sample => (draw b cell scale sample).1))
         FiniteQuery.collect expectedCurrent sharedKeys fun sharedWords =>
           let groups := expectedSelected sharedKeys sharedWords
           let keys := orderedInputs childInputCode (childInputCode_injective M target.length)
             (actionCurrentInputCover groups ∪ actionCurrentInputCover actions)
           FiniteQuery.collect expectedCurrent keys
             (expectedNext earlierKeys earlierWords groups actions keys)) := by
  have hshared : querySharedInputCover source target parent N F exponent Q a.value
      (fun _ => (initial q).1.value) q (fun b cell scale sample => (draw b cell scale sample).1) =
      querySharedInputCover source target parent N F exponent Q a.value
        (fun r => (initial r).1.value) q (fun b cell scale sample => (draw b cell scale sample).1) := rfl
  unfold queryRefinementGather
  dsimp only [BitQuery.compute, BitQuery.bind]
  apply BitQuery.Refines.charge
  rw [BinaryFraction.queryEarlierInputsWithWork_value M parent N P F exponent t hP a initial q R hR]
  apply BitQuery.Refines.collect readEarlier expectedEarlier he
  intro earlierWords
  apply BitQuery.Refines.charge
  apply BitQuery.Refines.charge
  apply BitQuery.Refines.charge
  rw [BinaryFraction.querySharedInputsWithWork_value source target, hshared]
  apply BitQuery.Refines.collect readCurrent expectedCurrent hc
  intro sharedWords
  apply BitQuery.Refines.charge
  apply BitQuery.Refines.charge
  rw [queryNeededInputsWithWork_value, ho, hs]
  apply BitQuery.Refines.collect readCurrent expectedCurrent hc
  intro words
  let ek := orderedInputs historyInputCode (historyInputCode_injective M target.length)
    (queryEarlierInputCover parent N P F exponent t a.value (fun r => (initial r).1.value) q)
  let sk := orderedInputs childInputCode (childInputCode_injective M target.length)
    (querySharedInputCover source target parent N F exponent Q a.value
      (fun r => (initial r).1.value) q (fun b cell scale sample => (draw b cell scale sample).1))
  let ck := orderedInputs childInputCode (childInputCode_injective M target.length)
    (actionCurrentInputCover (expectedSelected sk (sharedWords.map BinaryFraction.value)) ∪
      actionCurrentInputCover (expectedOnline ek (earlierWords.map BinaryFraction.value)))
  have hnext := hn ek earlierWords (selected sk sharedWords).1 (online ek earlierWords).1 ck words
  simpa only [ek, sk, ck, ho, hs] using hnext

end Simulation
end EditApproximation

end OAI
