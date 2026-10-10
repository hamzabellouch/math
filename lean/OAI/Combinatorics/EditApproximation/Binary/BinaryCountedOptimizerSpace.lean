import OAI.Combinatorics.EditApproximation.Binary.BinarySelectionSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandActionReads
import OAI.Combinatorics.EditApproximation.Queries.QueryBufferSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryOnlineSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem countedBandCoordinateAllocation_le_work {M n : ℕ} (mass : Vector BinaryFraction M)
    (total : BinaryFraction) (action : Fin M → TargetInterval n) (coordinate : Fin M × TargetInterval n) :
    countedBandCoordinateAllocation mass total action coordinate ≤
      (countedBandCoordinateWithWork mass total action coordinate).2 := by
  have hc := coordinateEqualAllocation_le_work coordinate (coordinate.1, action coordinate.1)
  have hd := divAllocation_le_work (mass.get coordinate.1) total
  unfold countedBandCoordinateAllocation countedBandCoordinateWithWork
  dsimp only
  split_ifs <;> (try dsimp only) <;> omega



theorem countedBandVerticesAllocation_le_work {M n d : ℕ} (coordinates : Vector (Fin M × TargetInterval n) d)
    (mass : Vector BinaryFraction M) (band : List (Fin M → TargetInterval n)) :
    countedBandVerticesAllocation coordinates mass band ≤ (countedBandVerticesWithWork coordinates mass band).2 := by
  have hm := bandMassAllocation_le_work mass
  have hs : (band.map fun action => vectorMapAllocation d fun i =>
      countedBandCoordinateAllocation mass (bandMassTotalWithWork mass).1 action (coordinates.get i)).sum ≤
      (band.map fun action => (vectorMapWithWork d fun i =>
        countedBandCoordinateWithWork mass (bandMassTotalWithWork mass).1 action (coordinates.get i)).2).sum := by
    induction band with
    | nil => simp
    | cons a rest ih =>
      have h := vectorMapAllocation_le_work d
        (fun i => countedBandCoordinateWithWork mass (bandMassTotalWithWork mass).1 a (coordinates.get i))
        (fun i => countedBandCoordinateAllocation mass (bandMassTotalWithWork mass).1 a (coordinates.get i))
        (fun i => countedBandCoordinateAllocation_le_work _ _ _ _)
      simp only [List.map_cons, List.sum_cons]
      omega
  unfold countedBandVerticesAllocation countedBandVerticesWithWork
  simp only [List.map_map, Function.comp_def]
  omega

/-- Arithmetic and labeled-vector allocation after coordinate construction.
Coordinate construction itself is accounted by its separate list allocator. -/


theorem countedPreparedActionKernelAllocation_le_work {M n : ℕ} (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (footprint : ℕ → Fin M × TargetInterval n → ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t : ℕ)
    (h : ∀ s coordinate, footprint s coordinate ≤ (read s coordinate).2) :
    countedPreparedActionKernelAllocation mass read footprint eta kappa band G j t ≤
      2 * (countedPreparedActionReadWithWork mass read eta kappa band G j t).2 := by
  let coordinates := (coordinateVectorWithWork band).1
  have hv := countedBandVerticesAllocation_le_work coordinates mass band
  have hl := vectorMapAllocation_le_work _
    (fun i => onlineLinearReadWithWork (fun child => mass.get child) read eta kappa t (coordinates.get i))
    (fun i => onlineLinearReadAllocation (fun child => mass.get child) read footprint eta kappa t (coordinates.get i))
    (fun i => onlineLinearReadAllocation_le_work _ _ _ _ _ _ _ (fun s _ => h s _))
  have hs := selectionAllocation_le_work (countedBandVerticesWithWork coordinates mass band).1
    (vectorMapWithWork _ fun i => onlineLinearReadWithWork (fun child => mass.get child)
      read eta kappa t (coordinates.get i)).1 G j
  unfold countedPreparedActionKernelAllocation countedPreparedActionReadWithWork
  dsimp only [coordinates] at hv hl hs ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
