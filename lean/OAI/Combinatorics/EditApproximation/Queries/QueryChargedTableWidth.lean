import OAI.Combinatorics.EditApproximation.Queries.QueryChargedFamily
import OAI.Combinatorics.EditApproximation.Queries.QueryWarmupWidth
import OAI.Combinatorics.EditApproximation.Queries.QueryBoundedActiveCost

namespace OAI

namespace EditApproximation
open BinaryFraction

section Table
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF B : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (oracle : ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent) → BinaryFraction)

theorem queryChargedFamilyTable_width
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hs : Nat.size source.length + 2 ≤ B) (ht : Nat.size target.length + 2 ≤ B)
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hMb : Nat.size M ≤ B) (ha : (a parent.val.pass).width ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B)
    (hactive : ∀ (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J),
      ((queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
        tau (a parent.val.pass) eta kappa delta T S passes copies parent hindex hbelow).value
        (fun key => oracle (Sum.map id (fun child =>
          ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩) key))).width ≤
        preparedKernelWordBudget M B) :
    ((queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa
      delta multiplier occurrence symbolBits positionBits parent).value oracle).width ≤
        localWarmupWordBudget M B + preparedKernelWordBudget M B := by
  let tableOracle := fun key => oracle (Sum.inr key)
  have hw := queryChargedWarmup_width source target N P F B (A parent.val.pass) (a parent.val.pass)
    multiplier parent occurrence symbolBits positionBits tableOracle hB hP hN hPb hFb hFpos hs ht ht'
    hinit hMb ha hv
  have hi := queryPhysicalInitial_width source target N P F B (A parent.val.pass) (a parent.val.pass)
    multiplier parent occurrence symbolBits positionBits tableOracle parent.val.state hP ht' hinit
  have hsmall : B ≤ localWarmupWordBudget M B := by
    unfold localWarmupWordBudget physicalContinuationInputBudget
    dsimp only
    omega
  unfold queryChargedFamilyTable
  simp only [BitQuery.value]
  split
  · simp only [BitQuery.mapKeysWithWork_value]
    exact hw.trans (Nat.le_add_right _ _)
  · split
    · split
      · simp only [BitQuery.value, BitQuery.mapKeysWithWork_value]
        exact hi.trans (hsmall.trans (Nat.le_add_right _ _))
      · rename_i hindex hbelow hlong
        simp only [BitQuery.value, BitQuery.mapKeysWithWork_value]
        exact (hactive _ _).trans (Nat.le_add_left _ _)
    · simp only [BitQuery.value, BitQuery.mapKeysWithWork_value]
      exact hi.trans (hsmall.trans (Nat.le_add_right _ _))

end Table
end EditApproximation

end OAI
