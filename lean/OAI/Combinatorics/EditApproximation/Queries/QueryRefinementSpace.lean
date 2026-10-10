import OAI.Combinatorics.EditApproximation.Queries.QueryGatherSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalSelectorSpace
import OAI.Combinatorics.EditApproximation.Queries.QuerySharedSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryContinuationSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalRefinement

namespace OAI

namespace EditApproximation
open BitQuery

section Local
variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (draw : CountedCellGroupDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (parentAllocation : TargetInterval target.length → ℕ)
  (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)
  (drawAllocation : CountedCellGroupAllocations M F Q)
  (integerAllocation : ℕ → TargetInterval target.length → ℕ)
  (hp : ∀ r, parentAllocation r ≤ (parentInitial r).2)
  (hca : ∀ i r, childAllocation i r ≤ (child i r).2)
  (hia : ∀ i r, initialAllocation i r ≤ (initial i r).2)
  (hd : ∀ b cell s j, drawAllocation b cell s j ≤ (draw b cell s j).2)
  (hz : ∀ b r, integerAllocation b r ≤ (integer b r).2)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (he : ∀ key, Heap (readEarlier key)) (hr : ∀ key, Heap (readCurrent key))

open BinaryFraction in
def queryLocalRefinementHeap : Heap (queryLocalRefinement source target parent N P F exponent H Q eM eF
    hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer q readEarlier readCurrent) :=
  (Heap.computeOf (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q)
    (queryEarlierInputsAllocation M parent N P F exponent t hP a parentInitial parentAllocation q)
    (queryEarlierInputsAllocation_le_work M parent N P F exponent t hP a parentInitial parentAllocation q hp)).bind _
    fun earlierKeys => Heap.collect readEarlier he earlierKeys _ fun earlierWords =>
      (Heap.compute (queryOnlineSelectWithWork source target parent N P F exponent H hP
        tau a eta kappa parentInitial child initial R hc hi t integer earlierKeys earlierWords q)
        (queryOnlineSelectAllocation source target parent N P F exponent H hP tau a eta kappa
          parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation
          t integer integerAllocation earlierKeys earlierWords q)
        (queryOnlineSelectAllocation_le_work source target parent N P F exponent H hP tau a eta kappa
          parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation
          t integer integerAllocation earlierKeys earlierWords q hp hca hia hz)).bind _ fun online =>
        Heap.chargeOf (parentAllocation q) (hp q)
          ((Heap.computeOf (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a (parentInitial q).1 q draw)
            (querySharedInputsAllocation M N F Q exponent eM eF hM hF parent a (parentInitial q).1 q draw drawAllocation)
            (querySharedInputsAllocation_le_work M N F Q exponent eM eF hM hF parent a (parentInitial q).1 q draw drawAllocation hd)).bind _
            fun sharedKeys => Heap.collect readCurrent hr sharedKeys _ fun sharedWords =>
              (Heap.computeOf (queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF
                tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)
                (queryGroupSelectAllocation source target parent N P F exponent Q eM eF hP hM hF tau a
                  parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation
                  draw drawAllocation sharedKeys sharedWords q)
                (queryGroupSelectAllocation_le_work source target parent N P F exponent Q eM eF hP hM hF tau a
                  parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation
                  draw drawAllocation sharedKeys sharedWords q hp hca hia hd)).bind _ fun groups =>
                (Heap.computeOf (queryNeededInputsWithWork groups online)
                  (queryNeededInputsAllocation groups online) (queryNeededInputsAllocation_le_work groups online)).bind _
                    fun currentKeys => Heap.collect readCurrent hr currentKeys _ fun currentWords =>
                      Heap.computeOf (queryRefinementFinishWithWork parent N P F a delta parentInitial t
                        earlierKeys earlierWords groups online currentKeys currentWords q)
                        (queryRefinementFinishAllocation parent N P F a delta parentInitial parentAllocation t
                          earlierKeys earlierWords groups online currentKeys currentWords q)
                        (queryRefinementFinishAllocation_le_work parent N P F a delta parentInitial parentAllocation t
                          earlierKeys earlierWords groups online currentKeys currentWords q hp))

end Local
end EditApproximation

end OAI
