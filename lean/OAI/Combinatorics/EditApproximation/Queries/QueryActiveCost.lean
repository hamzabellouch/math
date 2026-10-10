import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyActive
import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyRefinementCost
import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalProgramWidth
import OAI.Combinatorics.EditApproximation.Queries.QuerySemanticRestriction

namespace OAI

namespace EditApproximation

section Transport
variable {M J n : ℕ} (T : ℕ) (request : PhysicalTableRequest M J n)
  (hindex : T < request.index)

include hindex in
theorem queryRefinementRequest_eq :
    PhysicalTableRequest.refinement request.pass request.copy request.node T (request.index - T)
      request.state = request := by
  have hi : T + (request.index - T) = request.index := by omega
  unfold PhysicalTableRequest.refinement
  rw [hi]

def queryActiveChildMap {σ : Type*} (S : ℕ) :
    Sum σ {child : PhysicalTableRequest M J n // child.combinedRank T S <
      (PhysicalTableRequest.refinement request.pass request.copy request.node T (request.index - T)
        request.state).combinedRank T S} →
    Sum σ {child : PhysicalTableRequest M J n // child.combinedRank T S < request.combinedRank T S} :=
  Sum.map id (fun child => ⟨child.val, by simpa only [queryRefinementRequest_eq T request hindex] using child.property⟩)

def queryActiveOracle {σ : Type*} (S : ℕ)
    (oracle : Sum σ {child : PhysicalTableRequest M J n // child.combinedRank T S < request.combinedRank T S} →
      BinaryFraction) := fun key => oracle (queryActiveChildMap T request hindex S key)

def queryActiveReadWork {σ : Type*} (S : ℕ)
    (readWork : Sum σ {child : PhysicalTableRequest M J n // child.combinedRank T S < request.combinedRank T S} →
      ℕ) := fun key => 1 + readWork (queryActiveChildMap T request hindex S key)

end Transport

section Active
variable {α : Type*} {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF B E Scale : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (request : PhysicalTableRequest M J target.length)
  (hindex : T < request.index) (hbelow : request.node.1.val < J)
  (oracle : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
    {child : PhysicalTableRequest M J target.length // child.combinedRank T S < request.combinedRank T S} → BinaryFraction)
  (readWork : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
    {child : PhysicalTableRequest M J target.length // child.combinedRank T S < request.combinedRank T S} → ℕ)

local notation "tableOracle" => (fun key => queryActiveOracle T request hindex S oracle (Sum.inr key))
open BinaryFraction

theorem queryFamilyActive_work_bound (V C : ℕ)
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (request.index - T - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size (request.index - T) ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hV : 2 ≤ V) (hVB : V ≤ B) (hMean : warmupAverageWordBudget T V ≤ B)
    (hc : ∀ key, key.val.pass = request.pass → key.val.copy = request.copy → readWork (Sum.inr key) ≤ C)
    (hs : ∀ key, readWork (Sum.inl key) ≤ C)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ V)
    (hsv : ∀ key, (oracle (Sum.inl key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (oracle (Sum.inr key)).value)
    (hprior : ∀ input : Fin M × ℕ × TargetInterval target.length,
      ((queryPhysicalEarlierRead copies request.pass request.copy T S (request.index - T)
        request.node hbelow request.state input).value tableOracle).value ≤
      ((queryPhysicalWarmupRead copies request.pass request.copy T S (request.index - T)
        (Nat.sub_pos_of_lt hindex) request.node request.state
        (physicalChild request.node hbelow input.1) (by change request.node.1.val ≤ request.node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2.2).value tableOracle).value)
    (hp : Nat.size request.pass ≤ B) (hcopy : Nat.size request.copy ≤ B)
    (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
    (hbound : Nat.size (localOnlineMassBound M P H) ≤ B) :
    (queryFamilyActive (R := R) source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta T S passes copies request hindex hbelow).work oracle readWork ≤
      queryLocalProgramBitBudget M N P F exponent eM eF B Scale (request.index - T)
        (queryPhysicalDataBudget T J B V (C + 1) (queryFamilySourceReadBudget J B (C + 1 + 1))) := by
  rw [queryFamilyActive, BitQuery.mapKeysWithWork_work]
  change (queryFamilyRefinement (R := R) source target N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta passes copies request.pass request.copy T S (request.index - T)
    (Nat.sub_pos_of_lt hindex) request.node hbelow (Fin.ofNat R (request.index - T - 1)) request.state).work
    (queryActiveOracle T request hindex S oracle) (queryActiveReadWork T request hindex S readWork) ≤ _
  apply queryFamilyRefinement_work_bound source target N P F exponent H Q eM eF B E Scale hP hM hF
    tau a eta kappa delta passes copies request.pass request.copy T S (request.index - T)
    (Nat.sub_pos_of_lt hindex) request.node hbelow (Fin.ofNat R (request.index - T - 1)) request.state
    _ _ V (C + 1) hn htime hPd hV hVB hMean
  · intro key hpass hcopy'
    have h := hc ⟨key.val, by simpa only [queryRefinementRequest_eq T request hindex] using key.property⟩ hpass hcopy'
    change 1 + readWork (Sum.inr ⟨key.val, _⟩) ≤ C + 1
    omega
  · intro key
    change 1 + readWork (Sum.inl key) ≤ C + 1
    have := hs key
    omega
  · intro key
    exact hv _
  · exact hsv
  · intro key
    exact hnonneg _
  · exact hprior
  · exact hp
  · exact hcopy
  · exact hps
  · exact hcs
  · exact hbound

theorem queryFamilyActive_width
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (request.index - T - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size (request.index - T) ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (oracle (Sum.inr key)).value) :
    ((queryFamilyActive (R := R) source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta T S passes copies request hindex hbelow).value oracle).width ≤
      preparedKernelWordBudget M B := by
  rw [queryFamilyActive, BitQuery.mapKeysWithWork_value]
  apply queryFamilyRefinement_width source target N P F exponent H Q eM eF B E Scale hP hM hF
    tau a eta kappa delta passes copies request.pass request.copy T S (request.index - T)
    (Nat.sub_pos_of_lt hindex) request.node hbelow (Fin.ofNat R (request.index - T - 1)) request.state
    _ hn htime
  · intro key
    exact hv _
  · intro key
    exact hnonneg _

end Active
end EditApproximation

end OAI
