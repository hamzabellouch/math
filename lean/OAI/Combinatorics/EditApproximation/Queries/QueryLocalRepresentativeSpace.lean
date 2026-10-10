import OAI.Combinatorics.EditApproximation.Queries.QueryEligibilitySpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryWideSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryCellSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryCellReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem representativeScaleReadAllocation_le_work {n : ℕ} (P F : ℕ) (a : BinaryFraction)
    (read : TargetInterval n → BinaryFraction × ℕ) (allocation : TargetInterval n → ℕ)
    (radius : List Bool) (query : TargetInterval n) (e : ℕ)
    (h : ∀ r, allocation r ≤ (read r).2) :
    representativeScaleReadAllocation P F a read allocation radius query e ≤
      (representativeScaleReadWithWork P F a read radius query e).2 := by
  let b := 2 ^ e
  let spacing := (seedGridSpacingWithWork b P).1
  let points := (gridStateBoxWithWork n (bitWordValue spacing) (bitWordValue radius) query.lo query.hi).1
  let test := fun r => ((centerEligibilityWithWork b F a (read r).1).1,
    (centerEligibilityWithWork b F a (read r).1).2 + (read r).2)
  have hs := seedGridSpacingAllocation_le_work b P
  have hg := gridStateBoxAllocation_le_work n (bitWordValue spacing) (bitWordValue radius) query.lo query.hi
  have hf := filterAllocation_le_work test
    (fun r => centerEligibilityAllocation b F a (read r).1 + allocation r) points (by
      intro r _
      exact Nat.add_le_add (centerEligibilityAllocation_le_work b F a (read r).1) (h r))
  have hm := arithmeticMapAllocation_le_work (fun r => ((b, r), 1)) (fun _ => 1)
    (filterWithWork test points).1 (fun _ _ => le_rfl)
  unfold representativeScaleReadAllocation representativeScaleReadWithWork
  dsimp only [b, spacing, points, test] at hs hg hf hm ⊢
  omega



theorem localRepresentativeReadAllocation_le_work {n : ℕ} (N P F : ℕ) (a : BinaryFraction)
    (read : TargetInterval n → BinaryFraction × ℕ) (allocation : TargetInterval n → ℕ)
    (query : TargetInterval n) (h : ∀ r, allocation r ≤ (read r).2) :
    localRepresentativeReadAllocation N P F a read allocation query ≤
      (localRepresentativeReadWithWork N P F a read query).2 := by
  have hq := h query
  have hs := queryExponentsAllocation_le_work N F a (read query).1
  have hr := naturalCeilingAllocation_le_work (read query).1
  have hl := arithmeticFlatMapAllocation_le_work
    (representativeScaleReadWithWork P F a read (naturalCeilingWithWork (read query).1).1 query)
    (representativeScaleReadAllocation P F a read allocation (naturalCeilingWithWork (read query).1).1 query)
    (queryExponentsWithWork N F a (read query).1).1
    (fun e _ => representativeScaleReadAllocation_le_work P F a read allocation _ query e h)
  unfold localRepresentativeReadAllocation localRepresentativeReadWithWork
  dsimp only
  omega



theorem cellCentersReadAllocation_le_work {n : ℕ} (P F b : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction × ℕ) (allocation : TargetInterval n → ℕ)
    (cell : ℕ × ℕ) (h : ∀ r, allocation r ≤ (initial r).2) :
    cellCentersReadAllocation P F b a theta initial allocation cell ≤
      (cellCentersReadWithWork P F b a theta initial cell).2 := by
  let spacing := (seedGridSpacingWithWork b P).1
  let side := (canonicalMulWithWork theta (nat b)).1
  let states := (cellStatesWithWork n (bitWordValue spacing) side cell).1
  let test := fun r => ((centerEligibilityWithWork b F a (initial r).1).1,
    (initial r).2 + (centerEligibilityWithWork b F a (initial r).1).2)
  have hs := seedGridSpacingAllocation_le_work b P
  have hm := canonicalMulAllocation_le_work theta (nat b)
  have hg := cellStatesAllocation_le_work n (bitWordValue spacing) side cell
  have hf := filterAllocation_le_work test (fun r => allocation r + centerEligibilityAllocation b F a (initial r).1)
    states (fun r _ => Nat.add_le_add (h r) (centerEligibilityAllocation_le_work b F a (initial r).1))
  unfold cellCentersReadAllocation cellCentersReadWithWork
  dsimp only [spacing, side, states, test] at hg hf ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
