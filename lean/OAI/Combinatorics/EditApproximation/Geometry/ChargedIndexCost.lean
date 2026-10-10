import OAI.Combinatorics.EditApproximation.Geometry.RefinementRankCost

namespace OAI

/-! The charged request index distinguishes previous passes and coarse
leaves. For internal refinement its two index classes are exactly the
current and earlier table-read counters. -/

namespace EditApproximation

def chargedSameWeight {M J ny passes copies T S : ℕ}
    (parent child : ChargedPhysicalRequest M J ny passes copies T S) : ℕ :=
  if ¬ child.index < parent.index then 1 else 0

def chargedEarlierWeight {M J ny passes copies T S : ℕ}
    (parent child : ChargedPhysicalRequest M J ny passes copies T S) : ℕ :=
  if child.index < parent.index then 1 else 0

theorem chargedSameWeight_table {M J ny passes copies T S : ℕ}
    (parent : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S}) :
    chargedSameWeight (Sum.inr parent) = chargedTableWeight 0
      (fun child => if ¬ child.rank T S < parent.val.rank T S then 1 else 0) := by
  funext child
  cases child <;> simp only [chargedSameWeight, ChargedPhysicalRequest.index, chargedTableWeight,
    Nat.zero_lt_succ, not_true_eq_false, ite_false, Nat.add_lt_add_iff_right]

theorem chargedEarlierWeight_table {M J ny passes copies T S : ℕ}
    (parent : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S}) :
    chargedEarlierWeight (Sum.inr parent) = chargedTableWeight 1
      (fun child => if child.rank T S < parent.val.rank T S then 1 else 0) := by
  funext child
  cases child <;> simp only [chargedEarlierWeight, ChargedPhysicalRequest.index, chargedTableWeight,
    Nat.zero_lt_succ, ite_true, Nat.add_lt_add_iff_right]

section Costs

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
  (hshort : ¬ (physicalSourceInterval source.length parent.val.node).hi -
    (physicalSourceInterval source.length parent.val.node).lo ≤ 1)

include hindex hbelow hshort

theorem chargedGlobalQuery_current_cost :
    (chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial (Sum.inr parent)).cost
      (fun child => chargedRequestValue source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial child.val)
      (fun child => chargedSameWeight (Sum.inr parent) child.val) =
    (physicalRefinementDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
      (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow
      (group parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩ (Fin.ofNat R (parent.val.index - T - 1)))
      (integer parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩ (Fin.ofNat R (parent.val.index - T - 1)))
      parent.val.state).cost
      (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial child.val)
      (fun child => physicalCurrentReadWeight (T + (parent.val.index - T)) child.val) := by
  simp only [chargedSameWeight_table]
  rw [chargedGlobalQuery_refinement_cost source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta group integer initial parent hindex hbelow hshort]
  have hrank : (PhysicalTableRequest.refinement parent.val.pass parent.val.copy parent.val.node
      T (parent.val.index - T) parent.val.state).rank T S = parent.val.rank T S := by
    unfold PhysicalTableRequest.refinement PhysicalTableRequest.rank
    dsimp only
    congr 1
    omega
  rw [← hrank]
  exact physicalRefinementDataRequest_same_rank_cost source target N P F exponent H Q tau
    (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
    (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow _ _ parent.val.state _

theorem chargedGlobalQuery_earlier_cost :
    (chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial (Sum.inr parent)).cost
      (fun child => chargedRequestValue source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial child.val)
      (fun child => chargedEarlierWeight (Sum.inr parent) child.val) =
    (physicalRefinementDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
      (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow
      (group parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩ (Fin.ofNat R (parent.val.index - T - 1)))
      (integer parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩ (Fin.ofNat R (parent.val.index - T - 1)))
      parent.val.state).cost
      (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial child.val)
      (fun child => physicalEarlierReadWeight (T + (parent.val.index - T)) child.val) := by
  simp only [chargedEarlierWeight_table]
  rw [chargedGlobalQuery_refinement_cost source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta group integer initial parent hindex hbelow hshort]
  have hrank : (PhysicalTableRequest.refinement parent.val.pass parent.val.copy parent.val.node
      T (parent.val.index - T) parent.val.state).rank T S = parent.val.rank T S := by
    unfold PhysicalTableRequest.refinement PhysicalTableRequest.rank
    dsimp only
    congr 1
    omega
  rw [← hrank]
  exact physicalRefinementDataRequest_earlier_rank_cost source target N P F exponent H Q tau
    (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
    (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow _ _ parent.val.state _

end Costs

end EditApproximation

end OAI
