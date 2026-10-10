import OAI.Combinatorics.EditApproximation.Queries.QueryChargedTableCost
import OAI.Combinatorics.EditApproximation.Queries.QueryChargedTableWidth
import OAI.Combinatorics.EditApproximation.Queries.QueryBoundedSemanticCost

namespace OAI

namespace EditApproximation
attribute [local irreducible] queryFamilyBoundedActive queryFamilyActive queryFamilyRefinement
  queryPhysicalRandomDataRequest queryLocalProgram localRequestValue
open BinaryFraction

section Table
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF Amax B E Scale V C : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (oracle : ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent) → BinaryFraction)
  (readWork : ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent) → ℕ)
  (factor : ℕ → ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

local notation "requestValue" => localRequestValue source target N P F exponent H Q T S copies
  factor multiplier tau.value eta.value kappa.value delta.value group integer initial
local notation "activeBudget" => queryLocalProgramBitBudget M N P F exponent eM eF B Scale (parent.val.index - T)
  (queryPhysicalDataBudget T J B V (50 * B + 21 + (C + 1) + 1)
    (queryFamilySourceReadBudget J B (50 * B + 21 + (C + 1) + 1 + 1)))

theorem queryChargedFamilyTable_semantic_work_bound
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (parent.val.index - T - 1)
      tau (a parent.val.pass) eta kappa delta (fun _ _ => 0))
    (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hV : 2 ≤ V) (hVB : V ≤ B) (hMean : warmupAverageWordBudget T V ≤ B)
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hJ : Nat.size J ≤ B) (hi : Nat.size parent.val.index ≤ B)
    (hT : Nat.size T ≤ B) (hS : Nat.size S ≤ B)
    (hrank : Nat.size (parent.val.combinedRank T S) ≤ B)
    (hA : (A parent.val.pass).width ≤ B)
    (hAone : 1 ≤ (A parent.val.pass).value) (hAmax : (A parent.val.pass).value ≤ Amax)
    (hp : Nat.size parent.val.pass ≤ B) (hcopy : Nat.size parent.val.copy ≤ B)
    (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
    (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
    (hbound : Nat.size (localOnlineMassBound M P H) ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ V)
    (hsv : ∀ key, (oracle (Sum.inl key)).width ≤ B)
    (hc : ∀ key, readWork key ≤ C) (hdelta : 0 ≤ delta.value)
    (hread : ∀ child : {r : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S} //
        r.val.combinedRank T S < parent.val.combinedRank T S},
      (oracle (Sum.inr ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩)).value =
        requestValue child.val.val) :
    (queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa
      delta multiplier occurrence symbolBits positionBits parent).work oracle readWork ≤
        queryChargedTableBitBudget M P F Amax copies J symbolBits positionBits B C activeBudget := by
  have hMb : Nat.size M ≤ B := by have := hn.aritySize; omega
  have hFpos : 1 ≤ F := by rw [hF]; exact Nat.one_le_two_pow
  apply queryChargedFamilyTable_work_bound source target N P F exponent H Q eM eF Amax B C activeBudget
    hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent oracle readWork
    hn.largeBits hn.inputSize hn.precisionSize hn.factorSize hFpos hn.sourceSize hn.targetSize ht' hinit
    hMb hJ hi hT hA hn.factorWidth hAone hAmax hp hm (fun key => (hv key).trans hVB) hc
  intro hindex hbelow
  apply queryFamilyBoundedActive_work_bound source target N P F exponent H Q eM eF B E Scale hP hM hF
    tau (a parent.val.pass) eta kappa delta T S passes copies parent hindex hbelow _ _ V (C + 1) hn
    ((Nat.size_le_size (Nat.sub_le _ _)).trans hi) hPd hV hVB hMean
  · intro key
    have h := hc (Sum.map id (fun child =>
      ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩) key)
    omega
  · intro key
    exact hv _
  · exact hsv
  · intro child
    change (oracle (Sum.inr ⟨Sum.inr child.val, _⟩)).value ≥ 0
    rw [hread child]
    exact (localRequestValue_bounds source target N P F exponent H Q T S copies factor multiplier
      tau.value eta.value kappa.value delta.value group integer initial hdelta child.val.val).1
  · exact queryFamilyBoundedActive_history_bound source target N P F exponent H Q T S passes copies
      factor multiplier tau.value eta.value kappa.value delta.value group integer initial parent hindex hbelow
      _ hdelta hread
  · exact hp
  · exact hcopy
  · exact hps
  · exact hcs
  · exact hT
  · exact hS
  · exact hrank
  · exact hbound


theorem queryChargedFamilyTable_semantic_width
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (parent.val.index - T - 1)
      tau (a parent.val.pass) eta kappa delta (fun _ _ => 0))
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hi : Nat.size parent.val.index ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B) (hdelta : 0 ≤ delta.value)
    (hread : ∀ child : {r : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S} //
        r.val.combinedRank T S < parent.val.combinedRank T S},
      (oracle (Sum.inr ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩)).value =
        requestValue child.val.val) :
    ((queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa
      delta multiplier occurrence symbolBits positionBits parent).value oracle).width ≤
        localWarmupWordBudget M B + preparedKernelWordBudget M B := by
  have hFpos : 1 ≤ F := by rw [hF]; exact Nat.one_le_two_pow
  apply queryChargedFamilyTable_width source target N P F exponent H Q eM eF B hP hM hF A a tau eta kappa
    delta multiplier occurrence symbolBits positionBits parent oracle hn.largeBits hn.inputSize
    hn.precisionSize hn.factorSize hFpos hn.sourceSize hn.targetSize ht' hinit
    (by have := hn.aritySize; omega) hn.factorWidth hv
  intro hindex hbelow
  apply queryFamilyBoundedActive_width source target N P F exponent H Q eM eF B E Scale hP hM hF
    tau (a parent.val.pass) eta kappa delta T S passes copies parent hindex hbelow _ hn
    ((Nat.size_le_size (Nat.sub_le _ _)).trans hi)
  · intro child
    exact hv _
  · intro child
    change (oracle (Sum.inr ⟨Sum.inr child.val, _⟩)).value ≥ 0
    rw [hread child]
    exact (localRequestValue_bounds source target N P F exponent H Q T S copies factor multiplier
      tau.value eta.value kappa.value delta.value group integer initial hdelta child.val.val).1

end Table
end EditApproximation

end OAI
