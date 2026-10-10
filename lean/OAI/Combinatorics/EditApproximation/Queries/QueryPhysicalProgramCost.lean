import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalProgram
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalProgramCost
import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalReaderBounds
import OAI.Combinatorics.EditApproximation.Queries.QuerySourceWidths

namespace OAI

namespace EditApproximation.BinaryFraction

def queryPhysicalDataBudget (T J B V C W : ℕ) : ℕ :=
  W + (T + 1 + T * (7 * J + 30 + (C + 1) + 3) + warmupAverageBitBudget T V) +
    (8 * B + 7 * J + 32 + (C + 1)) + 1

end EditApproximation.BinaryFraction

namespace EditApproximation
section Physical
variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
  (N P F exponent H Q eM eF B E Scale : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction)
  (copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (readGroup : GroupScalarKey M F Q → BitQuery σ BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery σ BinaryFraction)
  (q : TargetInterval target.length)
  (oracle : Sum σ {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
    (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → BinaryFraction)
  (readWork : Sum σ {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
    (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → ℕ)

local notation "tableOracle" => (fun key => oracle (Sum.inr key))
local notation "sourceOracle" => (fun key => oracle (Sum.inl key))
local notation "sourceWork" => (fun key => 1 + readWork (Sum.inl key))

open BinaryFraction

theorem queryPhysicalRandomDataRequest_work_bound (V C W : ℕ)
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (t - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hV : 2 ≤ V) (hVB : V ≤ B) (hMean : warmupAverageWordBudget T V ≤ B)
    (hc : ∀ key, key.val.pass = pass → key.val.copy = copy → readWork (Sum.inr key) ≤ C)
    (hv : ∀ key, (tableOracle key).width ≤ V)
    (hnonneg : ∀ key, 0 ≤ (tableOracle key).value)
    (hprior : ∀ input : Fin M × ℕ × TargetInterval target.length,
      ((queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).value tableOracle).value ≤
        ((queryPhysicalWarmupRead copies pass copy T S t ht node q
          (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
          0 (Nat.zero_le T) input.2.2).value tableOracle).value)
    (hgW : ∀ key, ((readGroup key).value sourceOracle).width ≤ B)
    (hzW : ∀ key range, ((readInteger key range).value sourceOracle).width ≤ B)
    (hgR : ∀ key, queryGroupKeySize key ≤ 40 * B + 500 →
      (readGroup key).work sourceOracle sourceWork ≤ W)
    (hzR : ∀ key range, Nat.size key.1 ≤ B + 1 → Nat.size range ≤ 240 * (B + 5) + 7 →
      (readInteger key range).work sourceOracle sourceWork ≤ W) :
    (queryPhysicalRandomDataRequest source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q).work oracle readWork ≤
      queryLocalProgramBitBudget M N P F exponent eM eF B Scale t (queryPhysicalDataBudget T J B V C W) := by
  have htable : ∀ key, key.val.pass = pass → key.val.copy = copy →
      1 + readWork (Sum.inr key) ≤ C + 1 := fun key hp hc' => by have := hc key hp hc'; omega
  have hsmall : 7 * J + 30 + (C + 1) ≤ queryPhysicalDataBudget T J B V C W := by
    unfold queryPhysicalDataBudget; omega
  have hearlier : 8 * B + 7 * J + 32 + (C + 1) ≤ queryPhysicalDataBudget T J B V C W := by
    unfold queryPhysicalDataBudget; omega
  have hmass : T + 1 + T * (7 * J + 30 + (C + 1) + 3) + warmupAverageBitBudget T V ≤
      queryPhysicalDataBudget T J B V C W := by unfold queryPhysicalDataBudget; omega
  have hsource : W ≤ queryPhysicalDataBudget T J B V C W := by unfold queryPhysicalDataBudget; omega
  unfold queryPhysicalRandomDataRequest
  apply queryLocalProgram_work_bound source target (physicalSourceInterval source.length node)
    N P F exponent H Q eM eF B E Scale hP hM hF tau a eta kappa delta t _ _ _ _ _ q _ _
    oracle readWork _ hn ht htime hPd
  · intro r
    rw [BitQuery.mapKeysWithWork_value]
    exact (hv _).trans hVB
  · intro input
    rw [BitQuery.mapKeysWithWork_value]
    exact (queryPhysicalMassRead_bounds copies pass copy T S t ht node hbelow q tableOracle
      (fun key => 1 + readWork (Sum.inr key)) V (C + 1) htable hv input).1.trans hMean
  · intro input
    rw [BitQuery.mapKeysWithWork_value]
    exact (hv _).trans hVB
  · intro key
    simpa only [BitQuery.mapKeysWithWork_value] using hgW key
  · intro key range
    simpa only [BitQuery.mapKeysWithWork_value] using hzW key range
  · intro input
    rw [BitQuery.mapKeysWithWork_value]
    exact (queryPhysicalEarlierRead_width copies pass copy T S t node hbelow q tableOracle V hV hv input).trans hVB
  · intro input
    rw [BitQuery.mapKeysWithWork_value]
    exact (hv _).trans hVB
  · intro r
    rw [BitQuery.mapKeysWithWork_value]
    exact hnonneg _
  · intro input
    rw [BitQuery.mapKeysWithWork_value]
    exact hnonneg _
  · intro input
    rw [BitQuery.mapKeysWithWork_value]
    exact queryPhysicalEarlierRead_nonneg copies pass copy T S t node hbelow q tableOracle hnonneg input
  · intro input
    simpa only [BitQuery.mapKeysWithWork_value] using hprior input
  · intro r
    rw [BitQuery.mapKeysWithWork_work]
    exact (queryPhysicalWarmupRead_work_bound copies pass copy T S t ht node q tableOracle
      (fun key => 1 + readWork (Sum.inr key)) (C + 1) htable node le_rfl 0 (Nat.zero_le T) r).trans hsmall
  · intro input
    rw [BitQuery.mapKeysWithWork_work]
    exact (queryPhysicalMassRead_bounds copies pass copy T S t ht node hbelow q tableOracle
      (fun key => 1 + readWork (Sum.inr key)) V (C + 1) htable hv input).2.trans hmass
  · intro input
    rw [BitQuery.mapKeysWithWork_work]
    exact (queryPhysicalWarmupRead_work_bound copies pass copy T S t ht node q tableOracle
      (fun key => 1 + readWork (Sum.inr key)) (C + 1) htable _ _ 0 (Nat.zero_le T) input.2).trans hsmall
  · intro key hk
    rw [BitQuery.mapKeysWithWork_work]
    exact (hgR key hk).trans hsource
  · intro key range hk hr
    rw [BitQuery.mapKeysWithWork_work]
    exact (hzR key range hk hr).trans hsource
  · intro input hi
    rw [BitQuery.mapKeysWithWork_work]
    exact (queryPhysicalEarlierRead_work_bound copies pass copy T S t node hbelow q tableOracle
      (fun key => 1 + readWork (Sum.inr key)) B (C + 1) htable htime input hi).trans hearlier
  · intro input
    rw [BitQuery.mapKeysWithWork_work]
    exact (queryPhysicalCurrentRead_work_bound copies pass copy T S t node hbelow q tableOracle
      (fun key => 1 + readWork (Sum.inr key)) (C + 1) htable input).trans hsmall

end Physical
end EditApproximation

end OAI
