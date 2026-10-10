import OAI.Combinatorics.EditApproximation.Queries.QueryBoundedWork
import OAI.Combinatorics.EditApproximation.Queries.QueryHistorySemantic

namespace OAI

namespace EditApproximation

theorem queryRestrictedPhysicalOracle_nonneg {σ : Type*} {M J n : ℕ} (passes copies T S : ℕ)
    (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction)
    (hn : ∀ key, 0 ≤ (oracle key).value)
    (key : QueryPhysicalChild (σ := σ) passes copies T S parent) :
    0 ≤ (queryRestrictedPhysicalOracle passes copies T S parent oracle key).value := by
  unfold queryRestrictedPhysicalOracle BitQuery.restrictedOracle
  split
  · exact hn _
  · simp only [BinaryFraction.nat_value, Nat.cast_zero, le_refl]

section History
variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

local notation "requestValue" => localRequestValue source target N P F exponent H Q T S copies
  factor multiplier tau eta kappa delta group integer initial

theorem queryRestrictedPhysicalOracle_history_bound
    (passes pass copy t : ℕ) (ht : 0 < t) (htS : t ≤ S)
    (hpass : pass < passes) (hcopy : copy < copies) (hdelta : 0 ≤ delta)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval target.length)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (heq : parent.val = PhysicalTableRequest.refinement pass copy node T t q)
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction)
    (hread : ∀ key, (oracle (Sum.inr key)).value = requestValue key.val.val)
    (input : Fin M × ℕ × TargetInterval target.length) :
    let rawOracle := fun child : {r : PhysicalTableRequest M J target.length // r.combinedRank T S <
        (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} =>
      queryRestrictedPhysicalOracle passes copies T S parent oracle
        (Sum.inr ⟨child.val, by rw [heq]; exact child.property⟩)
    ((queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).value rawOracle).value ≤
      ((queryPhysicalWarmupRead copies pass copy T S t ht node q
        (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2.2).value rawOracle).value := by
  dsimp only
  apply queryPhysicalEarlierRead_history_bound source target N P F exponent H Q T S copies
    factor multiplier tau eta kappa delta group integer initial passes pass copy t ht htS
    hpass hcopy hdelta node hbelow q _ _ input
  intro child hb
  rw [queryRestrictedPhysicalOracle_table passes copies T S parent oracle _ hb]
  exact hread _

end History
end EditApproximation

end OAI
