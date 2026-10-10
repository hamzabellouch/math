import OAI.Combinatorics.EditApproximation.Binary.BinaryGridSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryBufferSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem cellCoordinatesAllocation_le_work (side : BinaryFraction) (p radius : ℕ) :
    cellCoordinatesAllocation side p radius ≤ (cellCoordinatesWithWork side p radius).2 := by
  let lower := (saturatingSubtractWithWork p radius).1
  let upper := (binaryNaturalAddWithWork p radius).1
  let firstQ := (divWithWork (nat (bitWordValue lower)) side).1
  let lastQ := (divWithWork (nat (bitWordValue upper)) side).1
  let first := (naturalFloorWithWork firstQ).1
  let last := (naturalFloorWithWork lastQ).1
  let stop := (binaryNaturalAddWithWork (bitWordValue last) 1).1
  have h1 := saturatingSubtractAllocation_le_work p radius
  have h2 := binaryNaturalAddAllocation_le_work p radius
  have h3 := divAllocation_le_work (nat (bitWordValue lower)) side
  have h4 := divAllocation_le_work (nat (bitWordValue upper)) side
  have h5 := naturalFloorAllocation_le_work firstQ
  have h6 := naturalFloorAllocation_le_work lastQ
  have h7 := binaryNaturalAddAllocation_le_work (bitWordValue last) 1
  have h8 := saturatingSubtractAllocation_le_work (bitWordValue stop) (bitWordValue first)
  unfold cellCoordinatesAllocation cellCoordinatesWithWork
  dsimp only [lower, upper, firstQ, lastQ, first, last, stop] at h3 h4 h5 h6 h7 h8 ⊢
  rw [List.length_range']
  omega



theorem targetCellsAllocation_le_work {n : ℕ} (side : BinaryFraction) (radius : ℕ) (q : TargetInterval n) :
    targetCellsAllocation side radius q ≤ (targetCellsWithWork side radius q).2 := by
  have hl := cellCoordinatesAllocation_le_work side q.lo radius
  have hr := cellCoordinatesAllocation_le_work side q.hi radius
  have hm := arithmeticFlatMapAllocation_le_work
    (fun lo => arithmeticMapWithWork (fun hi => ((lo, hi), 1)) (cellCoordinatesWithWork side q.hi radius).1)
    (fun _ => arithmeticMapAllocation (fun _ => 1) (cellCoordinatesWithWork side q.hi radius).1)
    (cellCoordinatesWithWork side q.lo radius).1 (fun _ _ =>
      arithmeticMapAllocation_le_work _ _ _ (fun _ _ => le_rfl))
  unfold targetCellsAllocation targetCellsWithWork
  dsimp only
  omega



theorem cellGridPointsAllocation_le_work (side : BinaryFraction) (g cell : ℕ) :
    cellGridPointsAllocation side g cell ≤ (cellGridPointsWithWork side g cell).2 := by
  let next := (binaryNaturalAddWithWork cell 1).1
  let lower := (canonicalMulWithWork (nat cell) side).1
  let upper := (canonicalMulWithWork (nat (bitWordValue next)) side).1
  let firstQ := (divWithWork lower (nat g)).1
  let lastQ := (divWithWork upper (nat g)).1
  let first := (naturalCeilingWithWork firstQ).1
  let last := (naturalCeilingWithWork lastQ).1
  let count := (saturatingSubtractWithWork (bitWordValue last) (bitWordValue first)).1
  let indices := List.range' (bitWordValue first) (bitWordValue count)
  have h1 := binaryNaturalAddAllocation_le_work cell 1
  have h2 := canonicalMulAllocation_le_work (nat cell) side
  have h3 := canonicalMulAllocation_le_work (nat (bitWordValue next)) side
  have h4 := divAllocation_le_work lower (nat g)
  have h5 := divAllocation_le_work upper (nat g)
  have h6 := naturalCeilingAllocation_le_work firstQ
  have h7 := naturalCeilingAllocation_le_work lastQ
  have h8 := saturatingSubtractAllocation_le_work (bitWordValue last) (bitWordValue first)
  have h9 := arithmeticMapAllocation_le_work (fun i =>
      (bitWordValue (binaryNaturalMulWithWork g i).1, (binaryNaturalMulWithWork g i).2 + Nat.size i + 2))
    (fun i => binaryNaturalMulAllocation g i + Nat.size i) indices (by
      intro i _
      have h := binaryNaturalMulAllocation_le_work g i
      dsimp only
      omega)
  unfold cellGridPointsAllocation cellGridPointsWithWork
  dsimp only [next, lower, upper, firstQ, lastQ, first, last, count, indices] at h3 h4 h5 h6 h7 h8 h9 ⊢
  omega



theorem cellStatesAllocation_le_work (n g : ℕ) (side : BinaryFraction) (cell : ℕ × ℕ) :
    cellStatesAllocation n g side cell ≤ (cellStatesWithWork n g side cell).2 := by
  have hl := cellGridPointsAllocation_le_work side g cell.1
  have hr := cellGridPointsAllocation_le_work side g cell.2
  have hm := arithmeticFlatMapAllocation_le_work
    (fun lo => filterMapWithWork (makeStateWithWork n lo) (cellGridPointsWithWork side g cell.2).1)
    (fun lo => filterMapAllocation (makeStateWithWork n lo) (makeStateAllocation n lo) (cellGridPointsWithWork side g cell.2).1)
    (cellGridPointsWithWork side g cell.1).1 (fun lo _ => filterMapAllocation_le_work _ _ _
      (fun hi _ => makeStateAllocation_le_work n lo hi))
  unfold cellStatesAllocation cellStatesWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
