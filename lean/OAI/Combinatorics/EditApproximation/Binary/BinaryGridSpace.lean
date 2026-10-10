import OAI.Combinatorics.EditApproximation.Queries.QueryCoordinateSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryWideGrid
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



theorem binaryNaturalAddAllocation_le_work (a b : ℕ) :
    binaryNaturalAddAllocation a b ≤ (binaryNaturalAddWithWork a b).2 := bitAddAllocation_le_work _ _ _



theorem binaryNaturalMulAllocation_le_work (a b : ℕ) :
    binaryNaturalMulAllocation a b ≤ (binaryNaturalMulWithWork a b).2 := bitMulAllocation_le_work _ _



theorem binaryNaturalDivAllocation_le_work (a b : ℕ) :
    binaryNaturalDivAllocation a b ≤ (binaryNaturalDivModWithWork a b).2.2 := bitDivModAllocation_le_work _ _



theorem naturalWordLEAllocation_le_work (a b : List Bool) :
    naturalWordLEAllocation a b ≤ (wordLEWithWork a b).2 := by
  have h := bitCompareWithWork_input_cells b a
  change a.length + b.length + 1 ≤ (bitCompareWithWork b a).2 + 1
  omega



theorem saturatingSubtractAllocation_le_work (a b : ℕ) :
    saturatingSubtractAllocation a b ≤ (saturatingSubtractWithWork a b).2 := by
  have hc := bitCompareWithWork_input_cells a.bits b.bits
  have hs := bitSubtractAllocation_le_work a.bits b.bits false
  unfold saturatingSubtractAllocation saturatingSubtractWithWork binaryNaturalCompareWithWork binaryNaturalSubtractWithWork
  dsimp only
  split_ifs <;> omega



theorem gridPointsAllocation_le_work (g lo hi : ℕ) :
    gridPointsAllocation g lo hi ≤ (gridPointsWithWork g lo hi).2 := by
  let lower := (bitCeilDivWithWork g.bits lo.bits).1
  let upper := (binaryNaturalDivModWithWork hi g).1
  let stop := (binaryNaturalAddWithWork (bitWordValue upper) 1).1
  let count := (saturatingSubtractWithWork (bitWordValue stop) (bitWordValue lower)).1
  let indices := List.range' (bitWordValue lower) (bitWordValue count)
  have hl := bitCeilDivAllocation_le_work g.bits lo.bits
  have hu := binaryNaturalDivAllocation_le_work hi g
  have hs := binaryNaturalAddAllocation_le_work (bitWordValue upper) 1
  have hc := saturatingSubtractAllocation_le_work (bitWordValue stop) (bitWordValue lower)
  have hm := arithmeticMapAllocation_with_spine
    (fun i => (bitWordValue (binaryNaturalMulWithWork g i).1, (binaryNaturalMulWithWork g i).2 + Nat.size i + 2))
    (fun i => binaryNaturalMulAllocation g i) indices
    (fun i _ => (binaryNaturalMulAllocation_le_work g i).trans (by omega))
  unfold gridPointsAllocation gridPointsWithWork
  dsimp only [lower, upper, stop, count, indices] at hl hu hs hc hm ⊢
  omega



theorem makeStateAllocation_le_work (n lo hi : ℕ) :
    makeStateAllocation n lo hi ≤ (makeStateWithWork n lo hi).2 := by
  have hl := naturalWordLEAllocation_le_work lo.bits hi.bits
  have hh := naturalWordLEAllocation_le_work hi.bits n.bits
  unfold makeStateAllocation makeStateWithWork
  dsimp only
  split_ifs <;> omega



theorem gridStateBoxAllocation_le_work (n g radius lo hi : ℕ) :
    gridStateBoxAllocation n g radius lo hi ≤ (gridStateBoxWithWork n g radius lo hi).2 := by
  let leftLow := (saturatingSubtractWithWork lo radius).1
  let leftHigh := (binaryNaturalAddWithWork lo radius).1
  let rightLow := (saturatingSubtractWithWork hi radius).1
  let rightHigh := (binaryNaturalAddWithWork hi radius).1
  let left := (gridPointsWithWork g (bitWordValue leftLow) (bitWordValue leftHigh)).1
  let right := (gridPointsWithWork g (bitWordValue rightLow) (bitWordValue rightHigh)).1
  have h1 := saturatingSubtractAllocation_le_work lo radius
  have h2 := binaryNaturalAddAllocation_le_work lo radius
  have h3 := saturatingSubtractAllocation_le_work hi radius
  have h4 := binaryNaturalAddAllocation_le_work hi radius
  have h5 := gridPointsAllocation_le_work g (bitWordValue leftLow) (bitWordValue leftHigh)
  have h6 := gridPointsAllocation_le_work g (bitWordValue rightLow) (bitWordValue rightHigh)
  have hf := arithmeticFlatMapAllocation_le_work
    (fun s => filterMapWithWork (makeStateWithWork n s) right)
    (fun s => filterMapAllocation (makeStateWithWork n s) (makeStateAllocation n s) right) left
    (fun s _ => filterMapAllocation_le_work (makeStateWithWork n s) (makeStateAllocation n s) right
      (fun k _ => makeStateAllocation_le_work n s k))
  unfold gridStateBoxAllocation gridStateBoxWithWork
  dsimp only [leftLow, leftHigh, rightLow, rightHigh, left, right] at h5 h6 hf ⊢
  omega

end EditApproximation

end OAI
