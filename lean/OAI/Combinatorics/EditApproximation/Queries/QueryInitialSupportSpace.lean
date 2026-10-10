import OAI.Combinatorics.EditApproximation.Queries.QueryInitialSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem initialCellAllocation_le_work (n P exponent : ℕ) (key : ℕ × ℕ × ℕ) :
    initialCellAllocation n P exponent key ≤
      (seedGridSpacingWithWork key.1 P).2 +
      (canonicalMulWithWork (inversePowerTwo exponent) (nat key.1)).2 +
      (cellStatesWithWork n (bitWordValue (seedGridSpacingWithWork key.1 P).1)
        (canonicalMulWithWork (inversePowerTwo exponent) (nat key.1)).1 key.2).2 + exponent + 3 := by
  have hs := seedGridSpacingAllocation_le_work key.1 P
  have hm := canonicalMulAllocation_le_work (inversePowerTwo exponent) (nat key.1)
  have hc := cellStatesAllocation_le_work n (bitWordValue (seedGridSpacingWithWork key.1 P).1)
    (canonicalMulWithWork (inversePowerTwo exponent) (nat key.1)).1 key.2
  unfold initialCellAllocation
  omega



theorem queryInitialSupportAllocation_le_work {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    queryInitialSupportAllocation N P F exponent hP a value q ≤
      (queryInitialSupportWithWork N P F exponent hP a value q).2 := by
  let build := fun key : ℕ × ℕ × ℕ =>
    let spacing := seedGridSpacingWithWork key.1 P
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat key.1)
    let states := cellStatesWithWork n (bitWordValue spacing.1) side.1 key.2
    (states.1, spacing.2 + side.2 + states.2 + exponent + 3)
  have hr := queryRawCentersAllocation_le_work N P F a value q
  have hg := queryGroupKeysAllocation_le_work N F exponent a value q
  have hc := arithmeticFlatMapAllocation_le_work build (initialCellAllocation n P exponent)
    (queryGroupKeysWithWork N F exponent a value q).1 (fun key _ => initialCellAllocation_le_work n P exponent key)
  have ho := queryOnlineKeysAllocation_le_work N P F hP a value q
  have hm := arithmeticMapAllocation_le_work (fun key : ℕ × TargetInterval n => (key.2, 1)) (fun _ => 1)
    (queryOnlineKeysWithWork N P F hP a value q).1 (fun _ _ => le_rfl)
  unfold queryInitialSupportAllocation queryInitialSupportWithWork
  dsimp only [build] at hc ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
