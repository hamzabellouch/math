import OAI.Combinatorics.EditApproximation.Queries.QueryBoundedActiveCost

namespace OAI

namespace EditApproximation
section History
variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
  (oracle : QueryBoundedChild (σ := σ) (passes + 1) copies T S parent → BinaryFraction)

local notation "requestValue" => localRequestValue source target N P F exponent H Q T S copies
  factor multiplier tau eta kappa delta group integer initial
local notation "rawOracle" => queryRestrictedPhysicalOracle (passes + 1) copies T S parent oracle
local notation "tableOracle" => (fun key => queryActiveOracle T parent.val hindex S rawOracle (Sum.inr key))

theorem queryBoundedSemantic_nonneg (hdelta : 0 ≤ delta)
    (hread : ∀ key, (oracle (Sum.inr key)).value = requestValue key.val.val)
    (key) : 0 ≤ (oracle (Sum.inr key)).value := by
  rw [hread]
  exact (localRequestValue_bounds source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta group integer initial hdelta key.val.val).1

theorem queryFamilyBoundedActive_history_bound (hdelta : 0 ≤ delta)
    (hread : ∀ key, (oracle (Sum.inr key)).value = requestValue key.val.val)
    (input : Fin M × ℕ × TargetInterval target.length) :
    ((queryPhysicalEarlierRead copies parent.val.pass parent.val.copy T S (parent.val.index - T)
      parent.val.node hbelow parent.val.state input).value tableOracle).value ≤
    ((queryPhysicalWarmupRead copies parent.val.pass parent.val.copy T S (parent.val.index - T)
      (Nat.sub_pos_of_lt hindex) parent.val.node parent.val.state
      (physicalChild parent.val.node hbelow input.1) (by change parent.val.node.1.val ≤ parent.val.node.1.val + 1; omega)
      0 (Nat.zero_le T) input.2.2).value tableOracle).value := by
  have ht : parent.val.index - T ≤ S := by have := parent.property.2.2; omega
  have h := queryRestrictedPhysicalOracle_history_bound source target N P F exponent H Q T S copies
    factor multiplier tau eta kappa delta group integer initial (passes + 1) parent.val.pass parent.val.copy
    (parent.val.index - T) (Nat.sub_pos_of_lt hindex) ht parent.property.1 parent.property.2.1 hdelta
    parent.val.node hbelow parent.val.state parent (queryRefinementRequest_eq T parent.val hindex).symm
    oracle hread input
  exact h

end History
end EditApproximation

end OAI
