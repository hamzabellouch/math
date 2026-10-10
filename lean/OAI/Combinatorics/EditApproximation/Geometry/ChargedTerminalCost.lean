import OAI.Combinatorics.EditApproximation.Geometry.ChargedQueryProgress
import OAI.Combinatorics.EditApproximation.Geometry.ChargedIndexCost
import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryCostOrder

namespace OAI

/-! Warmup and terminal queries have no same-index requests. Their
charged seed reads strictly decrease the pass index, including coarse
entries at pass zero. -/

namespace EditApproximation

theorem chargedWarmupQuery_same_cost_zero {α : Type*} [DecidableEq α] {M J passes copies T S : ℕ}
    (source target : List α) (N P F : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S}) (oracle) :
    (chargedWarmupQuery source target N P F factor multiplier parent).cost oracle
      (fun child => chargedSameWeight (Sum.inr parent) child.val) = 0 := by
  apply FiniteQuery.cost_eq_zero_of_keys
  intro key hk
  have h := chargedWarmupQuery_keys_earlier source target N P F factor multiplier parent oracle key hk
  exact ite_eq_right (not_not_intro h.2)

theorem chargedInitialQuery_same_cost_zero {α : Type*} [DecidableEq α] {M J passes copies T S : ℕ}
    (source target : List α) (N P F : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S}) (oracle) :
    (physicalInitialQuery source target N P F (factor parent.val.pass)
      (chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state)).cost oracle
      (fun child => chargedSameWeight (Sum.inr parent) child.val) = 0 := by
  apply FiniteQuery.cost_eq_zero_of_keys
  have hkeys := physicalInitialQuery_keys_all source target N P F (factor parent.val.pass)
    (chargedSeedQuery N multiplier parent) parent.val.node parent.val.state oracle
    (fun key => key.val.index < ChargedPhysicalRequest.index (Sum.inr parent))
    (fun q key hk => (chargedSeedQuery_keys_earlier N multiplier parent (parent.val.node, q) oracle key hk).2)
  intro key hk
  exact ite_eq_right (not_not_intro (hkeys key hk))

end EditApproximation

end OAI
