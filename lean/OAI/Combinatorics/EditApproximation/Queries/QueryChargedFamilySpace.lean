import OAI.Combinatorics.EditApproximation.Queries.QueryFamilySpace
import OAI.Combinatorics.EditApproximation.Queries.QueryChargedWarmupSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryChargedFamily

namespace OAI

namespace EditApproximation
open BitQuery

section Family
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)

def queryChargedFamilyTableHeap
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S}) :
    Heap (queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent) := by
  have hinit := queryPhysicalInitialHeap source target N P F (A parent.val.pass) (a parent.val.pass)
    multiplier parent occurrence symbolBits positionBits parent.val.state
  unfold queryChargedFamilyTable
  refine Heap.chargeOf (naturalWordLEAllocation parent.val.index.bits T.bits)
    ((naturalWordLEAllocation_le_work _ _).trans (Nat.le_succ _)) ?_
  split
  · exact (queryChargedWarmupHeap source target N P F (A parent.val.pass) (a parent.val.pass)
      multiplier parent occurrence symbolBits positionBits).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)
  · refine Heap.chargeOf (parent.val.node.1.val.bits.length + J.bits.length)
      ((bitCompareWithWork_input_cells _ _).trans (Nat.le_succ _)) ?_
    split
    · let interval := physicalSourceInterval source.length parent.val.node
      have hl := saturatingSubtractAllocation_le_work interval.hi interval.lo
      have ht := naturalWordLEAllocation_le_work (saturatingSubtractWithWork interval.hi interval.lo).1 [true]
      refine Heap.chargeOf (saturatingSubtractAllocation interval.hi interval.lo +
        naturalWordLEAllocation (saturatingSubtractWithWork interval.hi interval.lo).1 [true]) (by
          dsimp only [interval] at hl ht ⊢
          omega) ?_
      split
      · exact hinit.mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)
      · exact (queryFamilyBoundedActiveHeap (R := R) source target N P F exponent H Q eM eF hP hM hF
          tau (a parent.val.pass) eta kappa delta T S passes copies parent _ _).mapKeysWithWork _
          (fun _ => 1) (fun _ => le_rfl)
    · exact hinit.mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)

def queryChargedFamilyGlobalHeap
    (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
    (allocation : PhysicalEntry M J target.length → ℕ)
    (hc : ∀ entry, allocation entry ≤ 3 * (coarse entry).2)
    (request : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    Heap (queryChargedFamilyGlobal (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse request) := by
  cases request with
  | inl entry => exact Heap.compute (coarse entry) (allocation entry) (hc entry)
  | inr parent =>
    exact queryChargedFamilyTableHeap (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent

end Family
end EditApproximation

end OAI
