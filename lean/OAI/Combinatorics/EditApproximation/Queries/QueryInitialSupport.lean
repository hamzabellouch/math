import OAI.Combinatorics.EditApproximation.Queries.QueryListWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryRefinementLists
import OAI.Combinatorics.EditApproximation.Geometry.LocalOnlineSourceQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Executed Boolean construction of the first adaptive refinement lists.
Their values are the original lists, including ordering and repetitions. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryScalesWithWork_value (N F : ℕ) (a value : BinaryFraction) :
    (queryScalesWithWork N F a value).1 = dyadicQueryWindow N value.value a.value F := by
  simp only [queryScalesWithWork, arithmeticMapWithWork_value, powerTwoWord_value,
    queryExponentsWithWork_value]



@[simp] theorem queryRawCentersWithWork_value {n : ℕ} (N P F : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    (queryRawCentersWithWork N P F a value q).1 =
      rawRefinementCenters N P F a.value value.value q := by
  have hg (b : ℕ) : (gridStateBoxWithWork n (seedGridSpacing b P)
      ⌈value.value⌉₊ q.lo q.hi).1 = localTargetStates n (seedGridSpacing b P) ⌈value.value⌉₊ q := by
    rw [gridStateBoxWithWork_value _ _ _ _ _ (by unfold seedGridSpacing; omega)]
    rfl
  simp only [queryRawCentersWithWork, queryEraseWithWork_value _ queryIntervalEqualWithWork_value,
    arithmeticFlatMapWithWork_value, seedGridSpacingWithWork_value _ _ hP,
    naturalCeilingWithWork_value, hg, queryScalesWithWork_value, rawRefinementCenters]



@[simp] theorem queryGroupKeysWithWork_value {n : ℕ} (N F exponent : ℕ)
    (a value : BinaryFraction) (q : TargetInterval n) :
    (queryGroupKeysWithWork N F exponent a value q).1 =
      localGroupQueryKeys N F exponent a.value (fun _ => value.value) q := by
  simp only [queryGroupKeysWithWork, arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value,
    queryScalesWithWork_value, targetCellsWithWork_value, naturalCeilingWithWork_value,
    canonicalMulWithWork_value, inversePowerTwo_value, nat_value, localGroupQueryKeys]



@[simp] theorem queryOnlineKeysWithWork_value {n : ℕ} (N P F : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    (queryOnlineKeysWithWork N P F hP a value q).1 =
      localOnlineSourceKeys N P F a.value (fun _ => value.value) q := by
  simp only [queryOnlineKeysWithWork, arithmeticMapWithWork_value, queryScalesWithWork_value,
    roundStateWithWork_value, seedGridSpacingWithWork_value _ _ hP, localOnlineSourceKeys]



@[simp] theorem queryInitialSupportWithWork_value {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    (queryInitialSupportWithWork N P F exponent hP a value q).1 =
      refinementInitialSupport N P F exponent a.value value.value q := by
  simp only [queryInitialSupportWithWork, queryRawCentersWithWork_value _ _ _ hP,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value, cellStatesWithWork_value,
    seedGridSpacingWithWork_value _ _ hP, canonicalMulWithWork_value, inversePowerTwo_value,
    nat_value, queryGroupKeysWithWork_value, queryOnlineKeysWithWork_value,
    localOnlineSourceKeys, List.map_map, refinementInitialSupport]
  rfl

end BinaryFraction
end EditApproximation

end OAI
