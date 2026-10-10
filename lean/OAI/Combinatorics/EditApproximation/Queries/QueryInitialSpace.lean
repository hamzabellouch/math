import OAI.Combinatorics.EditApproximation.Queries.QueryInitialSupport
import OAI.Combinatorics.EditApproximation.Queries.QueryEligibilitySpace
import OAI.Combinatorics.EditApproximation.Queries.QueryInputSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundingSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryCellSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem queryScalesAllocation_le_work (N F : ℕ) (a value : BinaryFraction) :
    queryScalesAllocation N F a value ≤ (queryScalesWithWork N F a value).2 := by
  have he := queryExponentsAllocation_le_work N F a value
  have hm := arithmeticMapAllocation_le_work (fun e => (bitWordValue (powerTwoWord e), e + 3))
    (fun e => e + 1) (queryExponentsWithWork N F a value).1 (fun _ _ => by dsimp only; omega)
  unfold queryScalesAllocation queryScalesWithWork
  dsimp only
  omega



theorem queryRawCentersAllocation_le_work {n : ℕ} (N P F : ℕ) (a value : BinaryFraction) (q : TargetInterval n) :
    queryRawCentersAllocation N P F a value q ≤ (queryRawCentersWithWork N P F a value q).2 := by
  let build := fun b =>
    let spacing := seedGridSpacingWithWork b P
    let states := gridStateBoxWithWork n (bitWordValue spacing.1) (bitWordValue (naturalCeilingWithWork value).1) q.lo q.hi
    (states.1, spacing.2 + states.2 + 1)
  have hs := queryScalesAllocation_le_work N F a value
  have hr := naturalCeilingAllocation_le_work value
  have hc := arithmeticFlatMapAllocation_le_work build (fun b => seedGridSpacingAllocation b P +
    gridStateBoxAllocation n (bitWordValue (seedGridSpacingWithWork b P).1)
      (bitWordValue (naturalCeilingWithWork value).1) q.lo q.hi) (queryScalesWithWork N F a value).1 (by
      intro b _
      have hg := gridStateBoxAllocation_le_work n (bitWordValue (seedGridSpacingWithWork b P).1)
        (bitWordValue (naturalCeilingWithWork value).1) q.lo q.hi
      have hs := seedGridSpacingAllocation_le_work b P
      dsimp only [build]
      omega)
  have he := queryEraseAllocation_le_work queryIntervalEqualWithWork queryIntervalEqualAllocation
    (arithmeticFlatMapWithWork build (queryScalesWithWork N F a value).1).1 queryIntervalEqualAllocation_le_work
  unfold queryRawCentersAllocation queryRawCentersWithWork
  dsimp only [build] at hc he ⊢
  omega



theorem queryGroupKeysAllocation_le_work {n : ℕ} (N F exponent : ℕ) (a value : BinaryFraction) (q : TargetInterval n) :
    queryGroupKeysAllocation N F exponent a value q ≤ (queryGroupKeysWithWork N F exponent a value q).2 := by
  let radius := (naturalCeilingWithWork value).1
  let build := fun b =>
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
    let cells := targetCellsWithWork side.1 (bitWordValue radius) q
    let labeled := arithmeticMapWithWork (fun cell => ((b, cell), 1)) cells.1
    (labeled.1, side.2 + cells.2 + labeled.2 + 2)
  have hs := queryScalesAllocation_le_work N F a value
  have hr := naturalCeilingAllocation_le_work value
  have hk := arithmeticFlatMapAllocation_le_work build (fun b =>
      let side := (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).1
      canonicalMulAllocation (inversePowerTwo exponent) (nat b) + targetCellsAllocation side (bitWordValue radius) q +
        arithmeticMapAllocation (fun _ => 1) (targetCellsWithWork side (bitWordValue radius) q).1)
      (queryScalesWithWork N F a value).1 (by
        intro b _
        have hm := canonicalMulAllocation_le_work (inversePowerTwo exponent) (nat b)
        have hc := targetCellsAllocation_le_work (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).1
          (bitWordValue radius) q
        have hl := arithmeticMapAllocation_le_work (fun cell => ((b, cell), 1)) (fun _ => 1)
          (targetCellsWithWork (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).1 (bitWordValue radius) q).1
          (fun _ _ => le_rfl)
        dsimp only [build]
        omega)
  unfold queryGroupKeysAllocation queryGroupKeysWithWork
  dsimp only [radius, build] at hk ⊢
  omega



theorem queryOnlineKeysAllocation_le_work {n : ℕ} (N P F : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    queryOnlineKeysAllocation N P F hP a value q ≤ (queryOnlineKeysWithWork N P F hP a value q).2 := by
  have hs := queryScalesAllocation_le_work N F a value
  have hk := arithmeticMapAllocation_le_work (fun b =>
    let spacing := seedGridSpacingWithWork b P
    let center := roundStateWithWork (bitWordValue spacing.1) (seedGridSpacingWithWork_pos b P hP) q
    ((b, center.1), spacing.2 + center.2 + 2)) (fun b =>
    seedGridSpacingAllocation b P + roundStateAllocation (bitWordValue (seedGridSpacingWithWork b P).1) q + 1)
      (queryScalesWithWork N F a value).1 (by
        intro b _
        have hs := seedGridSpacingAllocation_le_work b P
        have hr := roundStateAllocation_le_work (bitWordValue (seedGridSpacingWithWork b P).1)
          (seedGridSpacingWithWork_pos b P hP) q
        dsimp only
        omega)
  dsimp only at hk
  unfold queryOnlineKeysAllocation queryOnlineKeysWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
