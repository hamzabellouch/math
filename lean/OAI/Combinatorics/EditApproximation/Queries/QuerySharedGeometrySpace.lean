import OAI.Combinatorics.EditApproximation.Queries.QuerySharedGeometry
import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundingSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryWideSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



theorem queryGapStatesAllocation_le_work (n g anchor radius sourceLength gapRadius : ℕ) :
    queryGapStatesAllocation n g anchor radius sourceLength gapRadius ≤
      (queryGapStatesWithWork n g anchor radius sourceLength gapRadius).2 := by
  let lo := (saturatingSubtractWithWork anchor radius).1
  let hi := (binaryNaturalAddWithWork anchor radius).1
  let build := fun first =>
    let center := binaryNaturalAddWithWork first sourceLength
    let lower := saturatingSubtractWithWork (bitWordValue center.1) gapRadius
    let upper := binaryNaturalAddWithWork (bitWordValue center.1) gapRadius
    let right := gridPointsWithWork g (bitWordValue lower.1) (bitWordValue upper.1)
    let valid := filterMapWithWork (makeStateWithWork n first) right.1
    (valid.1, center.2 + lower.2 + upper.2 + right.2 + valid.2 + 4)
  let allocation := fun first =>
    let center := (binaryNaturalAddWithWork first sourceLength).1
    let lower := (saturatingSubtractWithWork (bitWordValue center) gapRadius).1
    let upper := (binaryNaturalAddWithWork (bitWordValue center) gapRadius).1
    let right := (gridPointsWithWork g (bitWordValue lower) (bitWordValue upper)).1
    binaryNaturalAddAllocation first sourceLength + saturatingSubtractAllocation (bitWordValue center) gapRadius +
      binaryNaturalAddAllocation (bitWordValue center) gapRadius + gridPointsAllocation g (bitWordValue lower) (bitWordValue upper) +
      filterMapAllocation (makeStateWithWork n first) (makeStateAllocation n first) right
  have hl := saturatingSubtractAllocation_le_work anchor radius
  have hh := binaryNaturalAddAllocation_le_work anchor radius
  have hg := gridPointsAllocation_le_work g (bitWordValue lo) (bitWordValue hi)
  have hb := arithmeticFlatMapAllocation_le_work build allocation
    (gridPointsWithWork g (bitWordValue lo) (bitWordValue hi)).1 (by
      intro first _
      let center := (binaryNaturalAddWithWork first sourceLength).1
      let lower := (saturatingSubtractWithWork (bitWordValue center) gapRadius).1
      let upper := (binaryNaturalAddWithWork (bitWordValue center) gapRadius).1
      have hc := binaryNaturalAddAllocation_le_work first sourceLength
      have hl := saturatingSubtractAllocation_le_work (bitWordValue center) gapRadius
      have hu := binaryNaturalAddAllocation_le_work (bitWordValue center) gapRadius
      have hg := gridPointsAllocation_le_work g (bitWordValue lower) (bitWordValue upper)
      have hf := filterMapAllocation_le_work (makeStateWithWork n first) (makeStateAllocation n first)
        (gridPointsWithWork g (bitWordValue lower) (bitWordValue upper)).1 (fun last _ => makeStateAllocation_le_work n first last)
      dsimp only [build, allocation, center, lower, upper] at hl hu hg hf ⊢
      omega)
  unfold queryGapStatesAllocation queryGapStatesWithWork
  dsimp only [lo, hi, build, allocation] at hg hb ⊢
  omega

namespace BinaryFraction



theorem queryGroupRoundedStatesAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (b exponent : ℕ) (cell : ℕ × ℕ) (i : Fin M) (h : BinaryFraction) :
    queryGroupRoundedStatesAllocation (ny := ny) parent b exponent cell i h ≤
      (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).2 := by
  let theta := inversePowerTwo exponent
  let spacing := (roundedSpacingWithWork theta h).1
  let child := (sourceChildWithWork parent i).1
  let offset := (saturatingSubtractWithWork child.lo parent.lo).1
  let base := (canonicalMulWithWork (nat cell.1) theta).1
  let position := (canonicalMulWithWork base (nat b)).1
  let floor := (naturalFloorWithWork position).1
  let anchor := (binaryNaturalAddWithWork (bitWordValue floor) (bitWordValue offset)).1
  let radius := (binaryNaturalMulWithWork 12 b).1
  let length := (saturatingSubtractWithWork child.hi child.lo).1
  let twice := (canonicalMulWithWork (nat 2) h).1
  let gap := (naturalCeilingWithWork twice).1
  have h1 := roundedSpacingAllocation_le_work theta h
  have h2 := sourceChildAllocation_le_work parent i
  have h3 := saturatingSubtractAllocation_le_work child.lo parent.lo
  have h4 := canonicalMulAllocation_le_work (nat cell.1) theta
  have h5 := canonicalMulAllocation_le_work base (nat b)
  have h6 := naturalFloorAllocation_le_work position
  have h7 := binaryNaturalAddAllocation_le_work (bitWordValue floor) (bitWordValue offset)
  have h8 := binaryNaturalMulAllocation_le_work 12 b
  have h9 := saturatingSubtractAllocation_le_work child.hi child.lo
  have h10 := canonicalMulAllocation_le_work (nat 2) h
  have h11 := naturalCeilingAllocation_le_work twice
  have h12 := queryGapStatesAllocation_le_work ny (bitWordValue spacing) (bitWordValue anchor)
    (bitWordValue radius) (bitWordValue length) (bitWordValue gap)
  unfold queryGroupRoundedStatesAllocation queryGroupRoundedStatesWithWork
  dsimp only [theta, spacing, child, offset, base, position, floor, anchor, radius, length, twice, gap]
    at h1 h3 h4 h5 h6 h7 h9 h11 h12 ⊢
  omega

end BinaryFraction
end EditApproximation

end OAI
