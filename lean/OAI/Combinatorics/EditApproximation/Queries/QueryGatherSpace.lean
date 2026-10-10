import OAI.Combinatorics.EditApproximation.Binary.BitQuerySpace
import OAI.Combinatorics.EditApproximation.Queries.QueryInitialSupportSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryHistorySpace
import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSourceSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryOnlineRangeSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryBandGather
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalBuffers
import OAI.Combinatorics.EditApproximation.Queries.QueryWarmupBuffers
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace BinaryFraction



theorem queryParentReadAllocation_le_work {n : ℕ} (keys : List (TargetInterval n))
    (words : List BinaryFraction) (r : TargetInterval n) :
    queryParentReadAllocation keys words r ≤ (queryParentReadWithWork keys words r).2 :=
  gatheredLookupAllocation_le_work _ _ _ _ _ (fun k _ => queryIntervalEqualAllocation_le_work r k)



theorem queryBandInputsAllocation_le_work {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (allocation : TargetInterval ny → ℕ)
    (q : TargetInterval ny) (ha : ∀ r, allocation r ≤ (initial r).2) :
    queryBandInputsAllocation M parent N P F exponent hP a initial allocation q ≤
      (queryBandInputsWithWork M parent N P F exponent hP a initial q).2 := by
  have hr := queryEarlierRepresentativesAllocation_le_work N P F exponent hP a initial allocation q ha
  have hw := queryWideInputsAllocation_le_work M parent P
    (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1
  unfold queryBandInputsAllocation queryBandInputsWithWork
  dsimp only
  omega



theorem queryWarmupInputsAllocation_le_work {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (allocation : TargetInterval ny → ℕ)
    (q : TargetInterval ny) (ha : ∀ r, allocation r ≤ (initial r).2) :
    queryWarmupInputsAllocation M parent N P F a initial allocation q ≤
      (queryWarmupInputsWithWork M parent N P F a initial q).2 := by
  have hr := localRepresentativeReadAllocation_le_work N P F a initial allocation q ha
  have hw := queryWideInputsAllocation_le_work M parent P (localRepresentativeReadWithWork N P F a initial q).1
  unfold queryWarmupInputsAllocation queryWarmupInputsWithWork
  dsimp only
  omega

end BinaryFraction

open BitQuery

def queryInitialGatherHeap {ι β : Type*} {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a : BinaryFraction) (q : TargetInterval n)
    (reader : TargetInterval n → BitQuery ι BinaryFraction) (hr : ∀ key, Heap (reader key))
    (next : List (TargetInterval n) → List BinaryFraction → BitQuery ι β)
    (hn : ∀ keys words, Heap (next keys words)) :
    Heap (queryInitialGather N P F exponent hP a q reader next) :=
  (hr q).bind _ fun value =>
    (Heap.computeOf (BinaryFraction.queryInitialSupportWithWork N P F exponent hP a value q)
      (BinaryFraction.queryInitialSupportAllocation N P F exponent hP a value q)
      (BinaryFraction.queryInitialSupportAllocation_le_work N P F exponent hP a value q)).bind _ fun keys =>
        Heap.collect reader hr keys (next keys) (hn keys)

def queryBandGatherHeap {ι β : Type*} {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (allocation : TargetInterval ny → ℕ)
    (ha : ∀ r, allocation r ≤ (initial r).2) (q : TargetInterval ny)
    (massReader initialReader : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction)
    (hm : ∀ key, Heap (massReader key)) (hi : ∀ key, Heap (initialReader key))
    (next : List (Fin M × TargetInterval ny) → List BinaryFraction → List BinaryFraction → BitQuery ι β)
    (hn : ∀ keys mass words, Heap (next keys mass words)) :
    Heap (queryBandGather M parent N P F exponent hP a initial q massReader initialReader next) :=
  (Heap.computeOf (BinaryFraction.queryBandInputsWithWork M parent N P F exponent hP a initial q)
    (BinaryFraction.queryBandInputsAllocation M parent N P F exponent hP a initial allocation q)
    (BinaryFraction.queryBandInputsAllocation_le_work M parent N P F exponent hP a initial allocation q ha)).bind _ fun keys =>
      Heap.collect massReader hm keys _ fun mass => Heap.collect initialReader hi keys _ (hn keys mass)

def queryGroupSourceGatherHeap {ι β : Type*} {n : ℕ} (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (a : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction × ℕ) (allocation : TargetInterval n → ℕ)
    (ha : ∀ r, allocation r ≤ (initial r).2) (q : TargetInterval n)
    (reader : GroupScalarKey M F Q → BitQuery ι BinaryFraction) (hr : ∀ key, Heap (reader key))
    (next : List (GroupScalarKey M F Q) → List BinaryFraction → BitQuery ι β)
    (hn : ∀ keys words, Heap (next keys words)) :
    Heap (queryGroupSourceGather M N F Q exponent eM eF hM hF a initial q reader next) :=
  Heap.chargeOf (allocation q) (ha q)
    ((Heap.computeOf (BinaryFraction.queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (initial q).1 q)
      (BinaryFraction.queryGroupSourceKeysAllocation M N F Q exponent eM eF hM hF a (initial q).1 q)
      (BinaryFraction.queryGroupSourceKeysAllocation_le_work M N F Q exponent eM eF hM hF a (initial q).1 q)).bind _ fun keys =>
        Heap.collect reader hr keys (next keys) (hn keys))

def queryOnlineSourceGatherHeap {ι β : Type*} {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F exponent H : ℕ) (hP : 0 < P) (tau a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (initialAllocation : TargetInterval ny → ℕ)
    (child : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (childAllocation : Fin M → TargetInterval ny → ℕ)
    (hi : ∀ r, initialAllocation r ≤ (initial r).2)
    (hc : ∀ i r, childAllocation i r ≤ (child i r).2) (q : TargetInterval ny)
    (reader : (ℕ × TargetInterval ny) → ℕ → BitQuery ι BinaryFraction)
    (hr : ∀ key range, Heap (reader key range))
    (next : List (ℕ × TargetInterval ny) → List BinaryFraction → BitQuery ι β)
    (hn : ∀ keys words, Heap (next keys words)) :
    Heap (queryOnlineSourceGather parent N P F exponent H hP tau a initial child q reader next) :=
  Heap.chargeOf (initialAllocation q) (hi q)
    ((Heap.computeOf (BinaryFraction.queryOnlineKeysWithWork N P F hP a (initial q).1 q)
      (BinaryFraction.queryOnlineKeysAllocation N P F hP a (initial q).1 q)
      (BinaryFraction.queryOnlineKeysAllocation_le_work N P F hP a (initial q).1 q)).bind _ fun keys =>
        Heap.collect _ (fun key =>
          (Heap.computeOf (BinaryFraction.queryOnlineRangeWithWork parent P exponent H tau child key)
            (BinaryFraction.queryOnlineRangeAllocation parent P exponent H tau child childAllocation key)
            (BinaryFraction.queryOnlineRangeAllocation_le_work parent P exponent H tau child childAllocation key hc)).bind _ (hr key))
          keys (next keys) (hn keys))

end EditApproximation

end OAI
