import OAI.Combinatorics.EditApproximation.Binary.BinaryGuardSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem anchorGuardAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (b : ℕ) (states : Fin M → TargetInterval ny) (i : Fin M) :
    anchorGuardAllocation parent r b states i ≤
      (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).lo).2 +
      (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).hi).2 +
      (binaryNaturalMulWithWork 6 b).2 +
      (naturalDistanceLeWithWork (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).lo).1
        (states i).lo (bitWordValue (binaryNaturalMulWithWork 6 b).1)).2 +
      (naturalDistanceLeWithWork (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).hi).1
        (states i).hi (bitWordValue (binaryNaturalMulWithWork 6 b).1)).2 + 3 := by
  have hl := translatedEndpointAllocation_le_work r.lo parent.lo (sourceChild parent i).lo
  have hr := translatedEndpointAllocation_le_work r.lo parent.lo (sourceChild parent i).hi
  have hm := binaryNaturalMulAllocation_le_work 6 b
  have hld := naturalDistanceLeAllocation_le_work
    (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).lo).1
    (states i).lo (bitWordValue (binaryNaturalMulWithWork 6 b).1)
  have hrd := naturalDistanceLeAllocation_le_work
    (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).hi).1
    (states i).hi (bitWordValue (binaryNaturalMulWithWork 6 b).1)
  unfold anchorGuardAllocation
  dsimp only
  omega



theorem bandPredicateReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (b : ℕ) (tau theta velocity : BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ) (states : Fin M → TargetInterval ny)
    (h : ∀ action ∈ actions, ∀ i, allocation i (action i) ≤ (read i (action i)).2) :
    bandPredicateReadAllocation parent r b tau theta velocity actions hne read allocation states ≤
      (bandPredicateReadWithWork parent r b tau theta velocity actions hne read states).2 := by
  have hz := zeroConnectionAllocation_le_work r.lo r.hi (List.ofFn states)
  have ha := allAllocation_with_spine (fun i : Fin M =>
    let leftAnchor := translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).lo
    let rightAnchor := translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).hi
    let radius := binaryNaturalMulWithWork 6 b
    let left := naturalDistanceLeWithWork leftAnchor.1 (states i).lo (bitWordValue radius.1)
    let right := naturalDistanceLeWithWork rightAnchor.1 (states i).hi (bitWordValue radius.1)
    (left.1 && right.1, leftAnchor.2 + rightAnchor.2 + radius.2 + left.2 + right.2 + 3))
    (anchorGuardAllocation parent r b states) (List.finRange M)
    (fun i _ => anchorGuardAllocation_le_work parent r b states i)
  have ht := bandToleranceAllocation_le_work tau theta b M
  have hc := allAllocation_le_work
    (cutGuardReadWithWork parent r actions hne read states velocity (bandToleranceWithWork tau theta b M).1)
    (cutGuardReadAllocation parent r actions hne read allocation states velocity (bandToleranceWithWork tau theta b M).1)
    (List.finRange M) (fun i _ => cutGuardReadAllocation_le_work parent r actions hne read allocation states velocity _ i h)
  simp only [List.length_finRange] at ha
  unfold bandPredicateReadAllocation bandPredicateReadWithWork
  dsimp only at ha hc ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
