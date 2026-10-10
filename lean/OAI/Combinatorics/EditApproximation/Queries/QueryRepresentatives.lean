import OAI.Combinatorics.EditApproximation.Queries.QueryInitialSupport
import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryCellReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Counted representative and child-coordinate lists for adaptive band
data gathers. All initial-table lookups are included in the work counter. -/

namespace EditApproximation
namespace BinaryFraction



theorem queryEarlierRepresentativesWithWork_value {n : ℕ} (N P F exponent : ℕ)
    (hP : 0 < P) (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction × ℕ)
    (q : TargetInterval n) (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R) :
    (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1 =
      queryEarlierRepresentatives N P F exponent a.value (fun r => (initial r).1.value) q := by
  have hl := (localRepresentativeReadWithWork_eq_cost N P F a initial q R hR).1
  have hc (b : ℕ) (cell : ℕ × ℕ) :=
    (cellCentersReadWithWork_eq_cost P F b a (inversePowerTwo exponent) initial cell R hR).1
  simp only [queryEarlierRepresentativesWithWork, hl, hc, localRepresentativesWithWork_value _ _ _ hP,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value,
    cellCentersWithWork_value _ _ _ _ _ _ _ hP, inversePowerTwo_value,
    queryGroupKeysWithWork_value, queryOnlineKeysWithWork_value,
    queryEarlierRepresentatives, localGroupQueryKeys, localOnlineSourceKeys]



@[simp] theorem queryWideInputsWithWork_value {nx ny : ℕ} (M : ℕ)
    (parent : TargetInterval nx) (P : ℕ) (hP : 0 < P)
    (representatives : List (ℕ × TargetInterval ny)) :
    (queryWideInputsWithWork M parent P representatives).1 = wideWarmupInputs parent P representatives := by
  simp only [queryWideInputsWithWork, queryEraseWithWork_value _ coordinateEqualWithWork_value,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value,
    wideChildGridWithWork_value _ _ _ _ _ hP, wideWarmupInputs]



theorem queryBandInputsWithWork_value {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R) :
    (queryBandInputsWithWork M parent N P F exponent hP a initial q).1 =
      refinementBandInputList parent N P F exponent a.value (fun r => (initial r).1.value) q := by
  simp only [queryBandInputsWithWork, queryWideInputsWithWork_value _ _ _ hP,
    queryEarlierRepresentativesWithWork_value _ _ _ _ hP _ _ _ R hR, refinementBandInputList]

end BinaryFraction
end EditApproximation

end OAI
