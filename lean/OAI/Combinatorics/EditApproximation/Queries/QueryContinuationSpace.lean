import OAI.Combinatorics.EditApproximation.Queries.QueryLocalRepresentativeSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryContinuationSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryRefinementFinish
import OAI.Combinatorics.EditApproximation.Binary.BinaryWarmupReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem endpointActionAllocation_le_work {ny M : ℕ} (center : TargetInterval ny)
    (states : Fin M → TargetInterval ny) :
    endpointActionAllocation center states ≤ (endpointActionWithWork center states).2 := by
  have h := endpointConnectionAllocation_le_work center states
  unfold endpointActionAllocation endpointActionWithWork
  dsimp only
  omega



theorem wideActionsFromRepresentativesAllocation_le_work {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ) :
    wideActionsFromRepresentativesAllocation M parent representatives P ≤
      (wideActionsFromRepresentativesWithWork M parent representatives P).2 := by
  apply arithmeticFlatMapAllocation_le_work
  intro br _
  have hw := wideActionGridAllocation_le_work M parent br.2 br.1 P
  have ha := arithmeticMapAllocation_le_work (fun states : Vector (TargetInterval ny) M => endpointActionWithWork br.2 states.get)
    (fun states => endpointActionAllocation br.2 states.get)
    (wideActionGridWithWork M parent br.2 br.1 P).1 (fun states _ => endpointActionAllocation_le_work br.2 states.get)
  dsimp only
  omega



theorem physicalContinuationReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P F : ℕ) (delta fallback : BinaryFraction)
    (old current : Fin M × TargetInterval ny → BinaryFraction × ℕ)
    (oldAllocation currentAllocation : Fin M × TargetInterval ny → ℕ)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (query : TargetInterval ny)
    (ho : ∀ input, oldAllocation input ≤ (old input).2)
    (hc : ∀ input, currentAllocation input ≤ (current input).2) :
    physicalContinuationReadAllocation parent representatives P F delta fallback old current oldAllocation currentAllocation groups online query ≤
      (physicalContinuationReadWithWork parent representatives P F delta fallback old current groups online query).2 := by
  have hw := wideActionsFromRepresentativesAllocation_le_work M parent representatives P
  have hl := canonicalMulAllocation_le_work (nat 128) (nat F)
  have hf := localContinuationReadAllocation_le_work endpointDistanceWithWork endpointDistanceAllocation
    (canonicalMulWithWork (nat 128) (nat F)).1 delta fallback old current oldAllocation currentAllocation query
    (wideActionsFromRepresentativesWithWork M parent representatives P).1 groups online
    (endpointDistanceAllocation_le_work query) ho hc
  unfold physicalContinuationReadAllocation physicalContinuationReadWithWork
  dsimp only
  omega



theorem queryRefinementFinishAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx) (N P F : ℕ)
    (a delta : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ)
    (initialAllocation : TargetInterval ny → ℕ) (t : ℕ)
    (earlierKeys : List (Fin M × ℕ × TargetInterval ny)) (earlierWords : List BinaryFraction)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (currentKeys : List (Fin M × TargetInterval ny)) (currentWords : List BinaryFraction)
    (query : TargetInterval ny) (hi : ∀ r, initialAllocation r ≤ (initial r).2) :
    queryRefinementFinishAllocation parent N P F a delta initial initialAllocation t earlierKeys earlierWords
      groups online currentKeys currentWords query ≤
      (queryRefinementFinishWithWork parent N P F a delta initial t earlierKeys earlierWords groups online currentKeys currentWords query).2 := by
  have hq := hi query
  have hr := localRepresentativeReadAllocation_le_work N P F a initial initialAllocation query hi
  have hf := physicalContinuationReadAllocation_le_work parent (localRepresentativeReadWithWork N P F a initial query).1
    P F delta (initial query).1
    (queryHistoryReadWithWork earlierKeys earlierWords (t - 1))
    (fun input => queryChildReadWithWork currentKeys currentWords input.1 input.2)
    (queryHistoryReadAllocation earlierKeys earlierWords (t - 1))
    (fun input => queryChildReadAllocation currentKeys currentWords input.1 input.2) groups online query
    (queryHistoryReadAllocation_le_work earlierKeys earlierWords (t - 1))
    (fun input => queryChildReadAllocation_le_work currentKeys currentWords input.1 input.2)
  unfold queryRefinementFinishAllocation queryRefinementFinishWithWork
  dsimp only
  omega



theorem localWarmupReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ)
    (initialAllocation : TargetInterval ny → ℕ) (child : Fin M × TargetInterval ny → BinaryFraction × ℕ)
    (childAllocation : Fin M × TargetInterval ny → ℕ) (query : TargetInterval ny)
    (hi : ∀ r, initialAllocation r ≤ (initial r).2)
    (hc : ∀ input, childAllocation input ≤ (child input).2) :
    localWarmupReadAllocation parent N P F a initial initialAllocation child childAllocation query ≤
      (localWarmupReadKernelWithWork parent N P F a initial child query).2 := by
  have hq := hi query
  have hr := localRepresentativeReadAllocation_le_work N P F a initial initialAllocation query hi
  have hw := wideActionsFromRepresentativesAllocation_le_work M parent
    (localRepresentativeReadWithWork N P F a initial query).1 P
  have hl := canonicalMulAllocation_le_work (nat 128) (nat F)
  have hb := bellmanReadAllocation_le_work endpointDistanceWithWork endpointDistanceAllocation
    (canonicalMulWithWork (nat 128) (nat F)).1 (initial query).1 child childAllocation query
    (wideActionsFromRepresentativesWithWork M parent (localRepresentativeReadWithWork N P F a initial query).1 P).1
    (fun action _ => endpointDistanceAllocation_le_work query action.center)
    (fun action _ i => hc (action.childState i))
  unfold localWarmupReadAllocation localWarmupReadKernelWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
