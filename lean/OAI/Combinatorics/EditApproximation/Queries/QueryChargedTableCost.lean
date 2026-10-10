import OAI.Combinatorics.EditApproximation.Queries.QueryChargedFamily
import OAI.Combinatorics.EditApproximation.Queries.QueryChargedWarmupCost

namespace OAI

namespace EditApproximation
open BinaryFraction

def queryChargedTableBitBudget (M P F Amax copies J symbolBits positionBits B C active : ℕ) : ℕ :=
  80 * (B + 1) + queryChargedWarmupBitBudget M P F Amax copies J symbolBits positionBits B (C + 1) + active

section Table
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF Amax B C active : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (oracle : ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent) → BinaryFraction)
  (readWork : ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent) → ℕ)

local notation "tableOracle" => (fun key => oracle (Sum.inr key))
local notation "tableWork" => (fun key => 1 + readWork (Sum.inr key))

theorem queryChargedFamilyTable_work_bound
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hs : Nat.size source.length + 2 ≤ B) (ht : Nat.size target.length + 2 ≤ B)
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hMb : Nat.size M ≤ B) (hJ : Nat.size J ≤ B) (hi : Nat.size parent.val.index ≤ B)
    (hT : Nat.size T ≤ B)
    (hA : (A parent.val.pass).width ≤ B) (ha : (a parent.val.pass).width ≤ B)
    (hAone : 1 ≤ (A parent.val.pass).value) (hAmax : (A parent.val.pass).value ≤ Amax)
    (hp : Nat.size parent.val.pass ≤ B) (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B) (hc : ∀ key, readWork key ≤ C)
    (hactive : ∀ (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J),
      (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
        tau (a parent.val.pass) eta kappa delta T S passes copies parent hindex hbelow).work
        (fun key => oracle (Sum.map id (fun child =>
          ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩) key))
        (fun key => 1 + readWork (Sum.map id (fun child =>
          ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩) key)) ≤ active) :
    (queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa
      delta multiplier occurrence symbolBits positionBits parent).work oracle readWork ≤
        queryChargedTableBitBudget M P F Amax copies J symbolBits positionBits B C active := by
  have hw := queryChargedWarmup_work_bound source target N P F Amax B (C + 1)
    (A parent.val.pass) (a parent.val.pass) multiplier parent occurrence symbolBits positionBits
    tableOracle tableWork hB hP hN hPb hFb hFpos hs ht ht' hinit hMb hJ hi hA ha hAone hAmax hp hm hv
    (fun key => by have := hc (Sum.inr key); omega)
  have hinitial := queryPhysicalInitial_work_bound source target N P F Amax B (C + 1)
    (A parent.val.pass) (a parent.val.pass) multiplier parent occurrence symbolBits positionBits
    tableOracle tableWork parent.val.state (by omega) hP hN hPb (by omega) (by omega) (by omega)
    hA ha hAone hAmax hp hm hv (fun key => by have := hc (Sum.inr key); omega)
  have hiw : (queryPhysicalInitial source target N P F (A parent.val.pass) (a parent.val.pass)
      multiplier parent occurrence symbolBits positionBits parent.val.state).work tableOracle tableWork ≤
      queryChargedWarmupBitBudget M P F Amax copies J symbolBits positionBits B (C + 1) := by
    apply hinitial.trans
    unfold queryChargedWarmupBitBudget
    dsimp only
    omega
  have hindexcost := wordLEWithWork_cost parent.val.index.bits T.bits
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len] at hindexcost
  have hdepth := binaryNaturalCompareWithWork_cost parent.val.node.1.val J
  have hn := (Nat.size_le_size (Nat.le_of_lt_succ parent.val.node.1.isLt)).trans hJ
  have htest := querySliceTest_cost source (physicalSourceInterval source.length parent.val.node) B (by omega)
  unfold queryChargedFamilyTable
  simp only [BitQuery.work]
  split
  · simp only [BitQuery.mapKeysWithWork_work]
    unfold queryChargedTableBitBudget
    omega
  · split
    · split
      · simp only [BitQuery.work, BitQuery.mapKeysWithWork_work]
        unfold queryChargedTableBitBudget
        omega
      · rename_i hindex hbelow hlong
        simp only [BitQuery.work, BitQuery.mapKeysWithWork_work]
        have h := hactive (Nat.lt_of_not_ge (fun h => hindex ((queryNaturalLEWithWork_value _ _).mpr h)))
          ((binaryNaturalCompareWithWork_lt _ _).mp hbelow)
        unfold queryChargedTableBitBudget
        omega
    · simp only [BitQuery.work, BitQuery.mapKeysWithWork_work]
      unfold queryChargedTableBitBudget
      omega

end Table
end EditApproximation

end OAI
