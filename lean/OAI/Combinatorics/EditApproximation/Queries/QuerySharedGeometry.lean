import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryInputs
import OAI.Combinatorics.EditApproximation.Geometry.ActualRoundedGroupInputs
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Boolean endpoint enumeration for the whole-cell shared-read cover.
The inner interval is centered at each computed left endpoint plus the
child length, exactly as in the published query's gap guard. -/

namespace EditApproximation



@[simp] theorem queryGapStatesWithWork_value (n g anchor radius sourceLength gapRadius : ℕ)
    (hg : 0 < g) :
    (queryGapStatesWithWork n g anchor radius sourceLength gapRadius).1 =
      gridGapStates n g anchor radius sourceLength gapRadius := by
  simp only [queryGapStatesWithWork, arithmeticFlatMapWithWork_value, filterMapWithWork_value,
    makeStateWithWork_value, gridPointsWithWork_value _ _ _ hg,
    saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value, gridGapStates]

namespace BinaryFraction



theorem queryGroupRoundedStatesWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b exponent : ℕ) (cell : ℕ × ℕ)
    (i : Fin M) (h : BinaryFraction) :
    (queryGroupRoundedStatesWithWork (ny := target.length) parent b exponent cell i h).1 =
      groupRoundedStateList source target parent b exponent cell i h.value := by
  unfold queryGroupRoundedStatesWithWork
  dsimp only
  rw [queryGapStatesWithWork_value _ _ _ _ _ _ (roundedSpacingWithWork_pos _ _)]
  simp only [roundedSpacingWithWork_value, sourceChildWithWork_value, saturatingSubtractWithWork_value,
    canonicalMulWithWork_value, nat_value, naturalFloorWithWork_value, inversePowerTwo_value,
    binaryNaturalAddWithWork_value, binaryNaturalMulWithWork_value, naturalCeilingWithWork_value,
    groupRoundedStateList, groupRoundSpacing,
    substring_length source _ _ (sourceChild parent i).valid]
  simp only [Nat.cast_ofNat, mul_assoc]

end BinaryFraction
end EditApproximation

end OAI
