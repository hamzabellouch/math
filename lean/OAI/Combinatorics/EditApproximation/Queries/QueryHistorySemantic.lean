import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalReaders
import OAI.Combinatorics.EditApproximation.Geometry.LocalSeedSequence

namespace OAI

namespace EditApproximation
section History
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

local notation "requestValue" => localRequestValue source target N P F exponent H Q T S copies
  factor multiplier tau eta kappa delta group integer initial
local notation "seed" pass => localSeedSequence source target N P F exponent H Q T S copies
  factor multiplier tau eta kappa delta group integer initial pass

theorem localRequestValue_bounds (hdelta : 0 ≤ delta) (request : PhysicalTableRequest M J target.length) :
    0 ≤ requestValue request ∧ requestValue request ≤
      stageInitial source target (seed request.pass) N P F (factor request.pass) (request.node, request.state) := by
  unfold localRequestValue unifiedPhysicalValue
  dsimp only
  split
  · exact physicalLocalWarmup_bounds source target _ N P F _ _ _
  · exact physicalLocalRefinement_bounds source target _ N P F exponent Q _ tau delta T hdelta _ _ _ _ _

theorem queryPhysicalEarlierRead_history_bound
    (passes pass copy t : ℕ) (ht : 0 < t) (htS : t ≤ S)
    (hpass : pass < passes) (hcopy : copy < copies) (hdelta : 0 ≤ delta)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval target.length)
    (oracle : {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
      (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → BinaryFraction)
    (hread : ∀ key, key.val.Bounded passes copies T S → (oracle key).value = requestValue key.val)
    (input : Fin M × ℕ × TargetInterval target.length) :
    ((queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).value oracle).value ≤
      ((queryPhysicalWarmupRead copies pass copy T S t ht node q
        (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2.2).value oracle).value := by
  have hinit :
      ((queryPhysicalWarmupRead copies pass copy T S t ht node q
        (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2.2).value oracle).value =
      stageInitial source target (seed pass) N P F (factor pass)
        (physicalChild node hbelow input.1, input.2.2) := by
    change (oracle _).value = _
    rw [hread _ ⟨hpass, hcopy, Nat.zero_le _⟩]
    rw [localRequestValue_warmup source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass copy _ 0 (Nat.zero_le T)]
    rfl
  rw [hinit]
  unfold queryPhysicalEarlierRead
  simp only [BitQuery.value]
  split
  · rename_i htime
    have htime' := (binaryNaturalCompareWithWork_lt _ _).mp htime
    change (oracle _).value ≤ _
    rw [hread _ ⟨hpass, hcopy, by change T + input.2.1 ≤ T + S; omega⟩]
    exact (localRequestValue_bounds source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial hdelta _).2
  · simp only [BitQuery.value, BinaryFraction.nat_value, Nat.cast_zero]
    exact stageInitial_nonneg_all_seeds source target (seed pass) N P F (factor pass) _

end History
end EditApproximation

end OAI
