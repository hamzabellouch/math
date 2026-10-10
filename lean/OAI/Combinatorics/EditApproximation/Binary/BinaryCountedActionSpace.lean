import OAI.Combinatorics.EditApproximation.Binary.BinaryCountedOptimizerSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryCoordinateSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryEnvelopeSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction

/-- All counted optimizer allocations, including coordinate construction. -/


theorem countedPreparedActionAllocation_le_work {M n : ℕ} (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (footprint : ℕ → Fin M × TargetInterval n → ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t : ℕ)
    (h : ∀ s coordinate, footprint s coordinate ≤ (read s coordinate).2) :
    countedPreparedActionAllocation mass read footprint eta kappa band G j t ≤
      3 * (countedPreparedActionReadWithWork mass read eta kappa band G j t).2 := by
  have hc := coordinateVectorAllocation_le_work band
  have hk := countedPreparedActionKernelAllocation_le_work mass read footprint eta kappa band G j t h
  have hlocal : (coordinateVectorWithWork band).2 ≤
      (countedPreparedActionReadWithWork mass read eta kappa band G j t).2 := by
    unfold countedPreparedActionReadWithWork
    dsimp only
    omega
  unfold countedPreparedActionAllocation
  omega



theorem countedBandActionAllocation_le_work {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (initialAllocation : Fin M → TargetInterval n → ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (footprint : ℕ → Fin M × TargetInterval n → ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t : ℕ)
    (hi : ∀ i state, initialAllocation i state ≤ (initial i state).2)
    (hr : ∀ s coordinate, footprint s coordinate ≤ (read s coordinate).2) :
    countedBandActionAllocation b initial initialAllocation read footprint eta kappa band G j t ≤
      3 * (countedBandActionReadWithWork b initial read eta kappa band G j t).2 := by
  have he := envelopeVectorReadAllocation_le_work b band initial initialAllocation (fun i action _ => hi i (action i))
  have hc := countedPreparedActionAllocation_le_work (envelopeVectorReadWithWork b band initial).1
    read footprint eta kappa band G j t hr
  unfold countedBandActionAllocation countedBandActionReadWithWork
  dsimp only
  omega

/-- The actual gathered-history specialization of the labeled action sampler. -/
def queryCountedActionAllocation {M n : ℕ} (mass : Vector BinaryFraction M)
    (keys : List (Fin M × ℕ × TargetInterval n)) (values : List BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t : ℕ) : ℕ :=
  countedPreparedActionAllocation mass (queryHistoryReadWithWork keys values)
    (queryHistoryReadAllocation keys values) eta kappa band G j t

theorem queryCountedActionAllocation_le_work {M n : ℕ} (mass : Vector BinaryFraction M)
    (keys : List (Fin M × ℕ × TargetInterval n)) (values : List BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t : ℕ) :
    queryCountedActionAllocation mass keys values eta kappa band G j t ≤
      3 * (countedPreparedActionReadWithWork mass (queryHistoryReadWithWork keys values)
        eta kappa band G j t).2 :=
  countedPreparedActionAllocation_le_work mass _ _ eta kappa band G j t
    (fun _ _ => queryHistoryReadAllocation_le_work _ _ _ _)

end EditApproximation.BinaryFraction

end OAI
