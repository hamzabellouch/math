import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalInitialCost
import OAI.Combinatorics.EditApproximation.Queries.QueryChargedWarmup
import OAI.Combinatorics.EditApproximation.Queries.QueryWarmupProgramCost

namespace OAI

namespace EditApproximation

def queryChargedWarmupBitBudget (M P F Amax copies J symbolBits positionBits B C : ℕ) : ℕ :=
  let I := queryPhysicalInitialBitBudget P F Amax copies J symbolBits positionBits B C
  80 * (B + 1) + I +
    BinaryFraction.queryWarmupProgramBitBudget M P F B (I + 7 * J + 33 + C)

section Warmup
variable (source target : List ℕ) {M J passes copies T S : ℕ}
  (N P F Amax B C : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (oracle : {child : ChargedPhysicalRequest M J target.length passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → BinaryFraction)
  (readWork : {child : ChargedPhysicalRequest M J target.length passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → ℕ)

theorem queryChargedWarmup_work_bound
    (hB : 10 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hs : Nat.size source.length + 2 ≤ B) (ht : Nat.size target.length + 2 ≤ B)
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hM : Nat.size M ≤ B) (hJ : Nat.size J ≤ B) (hi : Nat.size parent.val.index ≤ B)
    (hA : A.width ≤ B) (ha : a.width ≤ B) (hAone : 1 ≤ A.value) (hAmax : A.value ≤ Amax)
    (hp : Nat.size parent.val.pass ≤ B) (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
    (hv : ∀ key, (oracle key).width ≤ B) (hc : ∀ key, readWork key ≤ C) :
    (queryChargedWarmup source target N P F A a multiplier parent occurrence symbolBits positionBits).work
      oracle readWork ≤ queryChargedWarmupBitBudget M P F Amax copies J symbolBits positionBits B C := by
  let I := queryPhysicalInitialBitBudget P F Amax copies J symbolBits positionBits B C
  let reader := queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits
  have hiR (q : TargetInterval target.length) : (reader q).work oracle readWork ≤ I :=
    queryPhysicalInitial_work_bound source target N P F Amax B C A a multiplier parent occurrence
      symbolBits positionBits oracle readWork q (by omega) hP hN hPb (by omega) (by omega) (by omega)
      hA ha hAone hAmax hp hm hv hc
  have hiW (q : TargetInterval target.length) : ((reader q).value oracle).width ≤ B :=
    queryPhysicalInitial_width source target N P F B A a multiplier parent occurrence symbolBits positionBits
      oracle q hP ht' hinit
  have hzero := naturalEqualWithWork_cost parent.val.index 0 B hi (by simp)
  have hn := (Nat.size_le_size (Nat.le_of_lt_succ parent.val.node.1.isLt)).trans hJ
  have hdepth := binaryNaturalCompareWithWork_cost parent.val.node.1.val J
  have hdepth' : (binaryNaturalCompareWithWork parent.val.node.1.val J).2 ≤ 8 * B + 10 := by omega
  have htest := querySliceTest_cost source (physicalSourceInterval source.length parent.val.node) B (by omega)
  unfold queryChargedWarmup
  simp only [BitQuery.work]
  split
  · change (naturalEqualWithWork parent.val.index 0).2 + 1 + (reader parent.val.state).work oracle readWork ≤ _
    have h := hiR parent.val.state
    unfold queryChargedWarmupBitBudget
    dsimp only
    dsimp only [I] at h
    omega
  · rename_i hnonzero
    have hindex : 0 < parent.val.index :=
      Nat.pos_of_ne_zero (fun h => hnonzero ((naturalEqualWithWork_value _ _).mpr h))
    split
    · split
      · have h := hiR parent.val.state
        change (naturalEqualWithWork parent.val.index 0).2 + 1 +
          ((binaryNaturalCompareWithWork parent.val.node.1.val J).2 + 1 +
          (_ + (reader parent.val.state).work oracle readWork)) ≤ _
        unfold queryChargedWarmupBitBudget
        dsimp only
        dsimp only [I] at h
        omega
      · rename_i hbelow hlong
        have hcR (input : Fin M × TargetInterval target.length) :
            (queryChargedWarmupChild parent ((binaryNaturalCompareWithWork_lt _ _).mp hbelow) hindex input).work
              oracle readWork ≤ I + 7 * J + 33 + C := by
          exact (queryChargedRead_work_bound parent oracle readWork C hc _).trans (by omega)
        have hw := queryWarmupProgram_work_bound (physicalSourceInterval source.length parent.val.node)
          N P F B (I + 7 * J + 33 + C) hP a reader
          (queryChargedWarmupChild parent ((binaryNaturalCompareWithWork_lt _ _).mp hbelow) hindex) parent.val.state
          oracle readWork hB hN hF hFpos hPb hs ht hM ha hiW (fun input => hv _)
          (fun r => (hiR r).trans (by omega)) hcR
        change (naturalEqualWithWork parent.val.index 0).2 + 1 +
          ((binaryNaturalCompareWithWork parent.val.node.1.val J).2 + 1 +
          (_ + (queryWarmupProgram _ N P F a reader _ parent.val.state).work oracle readWork)) ≤ _
        unfold queryChargedWarmupBitBudget
        dsimp only
        dsimp only [I] at hw
        omega
    · have h := hiR parent.val.state
      change (naturalEqualWithWork parent.val.index 0).2 + 1 +
        ((binaryNaturalCompareWithWork parent.val.node.1.val J).2 + 1 +
        (reader parent.val.state).work oracle readWork) ≤ _
      unfold queryChargedWarmupBitBudget
      dsimp only
      dsimp only [I] at h
      omega

end Warmup
end EditApproximation

end OAI
