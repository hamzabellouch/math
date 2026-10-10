import OAI.Combinatorics.EditApproximation.Queries.QueryActiveCost

namespace OAI

namespace EditApproximation
section Bounded
variable {α : Type*} {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF B E Scale : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
  (oracle : QueryBoundedChild (σ := PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies) (passes + 1) copies T S parent → BinaryFraction)
  (readWork : QueryBoundedChild (σ := PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies) (passes + 1) copies T S parent → ℕ)

local notation "rawOracle" => queryRestrictedPhysicalOracle (passes + 1) copies T S parent oracle
local notation "rawWork" => queryRestrictedPhysicalReadWork (passes + 1) copies T S parent readWork
local notation "tableOracle" => (fun key => queryActiveOracle T parent.val hindex S rawOracle (Sum.inr key))
open BinaryFraction

theorem queryFamilyBoundedActive_work_bound (V C : ℕ)
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (parent.val.index - T - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size (parent.val.index - T) ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hV : 2 ≤ V) (hVB : V ≤ B) (hMean : warmupAverageWordBudget T V ≤ B)
    (hc : ∀ key, readWork key ≤ C)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ V)
    (hsv : ∀ key, (oracle (Sum.inl key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (oracle (Sum.inr key)).value)
    (hprior : ∀ input : Fin M × ℕ × TargetInterval target.length,
      ((queryPhysicalEarlierRead copies parent.val.pass parent.val.copy T S (parent.val.index - T)
        parent.val.node hbelow parent.val.state input).value tableOracle).value ≤
      ((queryPhysicalWarmupRead copies parent.val.pass parent.val.copy T S (parent.val.index - T)
        (Nat.sub_pos_of_lt hindex) parent.val.node parent.val.state
        (physicalChild parent.val.node hbelow input.1) (by change parent.val.node.1.val ≤ parent.val.node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2.2).value tableOracle).value)
    (hp : Nat.size parent.val.pass ≤ B) (hcopy : Nat.size parent.val.copy ≤ B)
    (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
    (hT : Nat.size T ≤ B) (hS : Nat.size S ≤ B)
    (hrank : Nat.size (parent.val.combinedRank T S) ≤ B)
    (hbound : Nat.size (localOnlineMassBound M P H) ≤ B) :
    (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta T S passes copies parent hindex hbelow).work oracle readWork ≤
      queryLocalProgramBitBudget M N P F exponent eM eF B Scale (parent.val.index - T)
        (queryPhysicalDataBudget T J B V (50 * B + 21 + C + 1)
          (queryFamilySourceReadBudget J B (50 * B + 21 + C + 1 + 1))) := by
  rw [queryFamilyBoundedActive, queryRestrictPhysicalBody_work]
  apply queryFamilyActive_work_bound source target N P F exponent H Q eM eF B E Scale hP hM hF
    tau a eta kappa delta T S passes copies parent.val hindex hbelow rawOracle rawWork V
    (50 * B + 21 + C) hn htime hPd hV hVB hMean
  · intro key _ hcopy'
    apply queryRestrictedPhysicalReadWork_bound (passes + 1) copies T S parent readWork B C
      hps ((Nat.size_le_size (Nat.le_succ copies)).trans hcs) hT hS hrank hcopy hc (Sum.inr key)
    intro child heq
    cases heq
    exact hcopy'
  · intro key
    apply queryRestrictedPhysicalReadWork_bound (passes + 1) copies T S parent readWork B C
      hps ((Nat.size_le_size (Nat.le_succ copies)).trans hcs) hT hS hrank hcopy hc (Sum.inl key)
    intro child heq
    cases heq
  · exact queryRestrictedPhysicalOracle_table_width (passes + 1) copies T S parent oracle V hV hv
  · intro key
    exact hsv key
  · exact queryRestrictedPhysicalOracle_table_nonneg (passes + 1) copies T S parent oracle hnonneg
  · exact hprior
  · exact hp
  · exact hcopy
  · exact hps
  · exact hcs
  · exact hbound

theorem queryFamilyBoundedActive_width
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (parent.val.index - T - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size (parent.val.index - T) ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (oracle (Sum.inr key)).value) :
    ((queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta T S passes copies parent hindex hbelow).value oracle).width ≤
      preparedKernelWordBudget M B := by
  rw [queryFamilyBoundedActive, queryRestrictPhysicalBody_value]
  apply queryFamilyActive_width source target N P F exponent H Q eM eF B E Scale hP hM hF
    tau a eta kappa delta T S passes copies parent.val hindex hbelow rawOracle hn htime
  · exact queryRestrictedPhysicalOracle_table_width (passes + 1) copies T S parent oracle B
      (by have := hn.largeBits; omega) hv
  · exact queryRestrictedPhysicalOracle_table_nonneg (passes + 1) copies T S parent oracle hnonneg

end Bounded
end EditApproximation

end OAI
