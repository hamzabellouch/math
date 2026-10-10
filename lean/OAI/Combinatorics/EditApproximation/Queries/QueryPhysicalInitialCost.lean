import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalInitial
import OAI.Combinatorics.EditApproximation.Queries.QueryInitialProgramCost
import OAI.Combinatorics.EditApproximation.Queries.QueryChargedSeedCost
import OAI.Combinatorics.EditApproximation.Coarse.CoarseDescriptorWork

namespace OAI

namespace EditApproximation

/-- The slice test reads only the stored endpoints; it does not materialize the substring. -/
theorem querySliceTest_cost {α : Type*} (source : List α) (interval : TargetInterval source.length)
    (B : ℕ) (hB : Nat.size source.length ≤ B) :
    (saturatingSubtractWithWork interval.hi interval.lo).2 +
      (wordLEWithWork (saturatingSubtractWithWork interval.hi interval.lo).1 [true]).2 + 2 ≤ 30 * B + 20 := by
  have hlo := (Nat.size_le_size (interval.ordered.trans interval.valid)).trans hB
  have hhi := (Nat.size_le_size interval.valid).trans hB
  have hs := saturatingSubtractWithWork_cost interval.hi interval.lo
  have hl := (saturatingSubtractWithWork_length interval.hi interval.lo).trans (max_le hhi hlo)
  have ht := wordLEWithWork_cost (saturatingSubtractWithWork interval.hi interval.lo).1 [true]
  simp only [List.length_cons, List.length_nil] at ht
  omega

def queryPhysicalInitialBitBudget (P _F Amax copies J symbolBits positionBits B C : ℕ) : ℕ :=
  30 * B + 20 + (10 * B + 2 * symbolBits + 4 * positionBits + B + 17) +
    BinaryFraction.queryInitialProgramBitBudget P Amax B (queryChargedSeedBitBudget copies J B C)

section Initial
variable (source target : List ℕ) {M J passes copies T S : ℕ}
  (N P F Amax B C : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (oracle : {child : ChargedPhysicalRequest M J target.length passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → BinaryFraction)
  (readWork : {child : ChargedPhysicalRequest M J target.length passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → ℕ)

theorem queryPhysicalInitial_work_bound (q : TargetInterval target.length)
    (hB : 8 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hF : Nat.size F ≤ B) (hs : Nat.size source.length ≤ B) (ht : Nat.size (target.length + 1) ≤ B)
    (hA : A.width ≤ B) (ha : a.width ≤ B) (hAone : 1 ≤ A.value) (hAmax : A.value ≤ Amax)
    (hp : Nat.size parent.val.pass ≤ B) (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
    (hv : ∀ key, (oracle key).width ≤ B) (hc : ∀ key, readWork key ≤ C) :
    (queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits q).work
        oracle readWork ≤ queryPhysicalInitialBitBudget P F Amax copies J symbolBits positionBits B C := by
  let interval := physicalSourceInterval source.length parent.val.node
  have htest := querySliceTest_cost source interval B hs
  have hseed (r : TargetInterval target.length) :=
    queryChargedSeedAt_bounds parent oracle readWork N B C multiplier r (by omega) hN hp hm hv hc
  have hlength : Nat.size (bitWordValue (saturatingSubtractWithWork interval.hi interval.lo).1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size ((Nat.sub_le _ _).trans interval.valid)).trans hs
  have hi := queryInitialConeProgramAt_work_bound
    (bitWordValue (saturatingSubtractWithWork interval.hi interval.lo).1) N P F Amax B
    (queryChargedSeedBitBudget copies J B C) hP A a (queryChargedSeedAt parent N multiplier) q
    oracle readWork hB hN hPb hF hlength
    ((Nat.size_le_size (Nat.le_succ target.length)).trans ht) hA ha hAone hAmax
    (fun r => (hseed r).1) (fun r => (hseed r).2)
  have hl := (queryIndexedSliceWithWork_cost source interval target.length q occurrence symbolBits positionBits B hs).trans
    (Nat.add_le_add_right (Nat.add_le_add_left ht _) 17)
  unfold queryPhysicalInitial
  simp only [BitQuery.work]
  split
  · simp only [BitQuery.compute, BitQuery.work, Nat.add_zero]
    change (saturatingSubtractWithWork interval.hi interval.lo).2 +
      (wordLEWithWork (saturatingSubtractWithWork interval.hi interval.lo).1 [true]).2 + 2 +
      (queryIndexedSliceWithWork source interval target.length q occurrence symbolBits positionBits).2 ≤ _
    exact (Nat.add_le_add htest hl).trans (by unfold queryPhysicalInitialBitBudget; omega)
  · change (saturatingSubtractWithWork interval.hi interval.lo).2 +
      (wordLEWithWork (saturatingSubtractWithWork interval.hi interval.lo).1 [true]).2 + 2 + _ ≤ _
    exact (Nat.add_le_add htest hi).trans (by unfold queryPhysicalInitialBitBudget; omega)

theorem queryPhysicalInitial_width (q : TargetInterval target.length)
    (hP : 0 < P) (hleaf : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B) :
    ((queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits q).value
      oracle).width ≤ B := by
  unfold queryPhysicalInitial
  simp only [BitQuery.value]
  split
  · exact (binaryIndexedLeafWithWork_bounds occurrence symbolBits positionBits _ q.lo q.hi).1.trans
      ((Nat.add_le_add_right (Nat.size_le_size (Nat.add_le_add_right q.valid 1)) 2).trans hleaf)
  · exact (queryInitialConeProgramAt_width _ N P F A a (queryChargedSeedAt parent N multiplier) q
      oracle hP).trans hinit

end Initial
end EditApproximation

end OAI
