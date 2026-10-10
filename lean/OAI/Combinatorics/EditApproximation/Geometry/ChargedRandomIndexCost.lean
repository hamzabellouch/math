import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomCost

namespace OAI

namespace EditApproximation

section Costs

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R → (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ) (answer : PhysicalTableRequest M J target.length → ℚ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
  (hshort : ¬ (physicalSourceInterval source.length parent.val.node).hi -
    (physicalSourceInterval source.length parent.val.node).lo ≤ 1)

include hindex hbelow hshort

theorem chargedRandomGlobalQuery_current_cost :
    (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial (Sum.inr parent)).cost
      (Sum.elim sourceAnswer (fun child => Sum.elim (fun entry => (initial entry : ℚ))
        (fun r => answer r.val) child.val))
      (Sum.elim (fun _ => 0) (fun child => chargedSameWeight (Sum.inr parent) child.val)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
      (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow
      (readGroup parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩ (Fin.ofNat R (parent.val.index - T - 1)))
      (readInteger parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩ (Fin.ofNat R (parent.val.index - T - 1)))
      parent.val.state).cost
      (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim (fun _ => 0) (fun child => physicalCurrentReadWeight (T + (parent.val.index - T)) child.val)) := by
  simp only [chargedSameWeight_table]
  rw [chargedRandomGlobalQuery_refinement_cost source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta readGroup readInteger initial sourceAnswer answer (fun _ => 0) _ _ parent hindex hbelow hshort]
  have hrank : (PhysicalTableRequest.refinement parent.val.pass parent.val.copy parent.val.node
      T (parent.val.index - T) parent.val.state).rank T S = parent.val.rank T S := by
    unfold PhysicalTableRequest.refinement PhysicalTableRequest.rank
    dsimp only
    congr 1
    omega
  rw [← hrank]
  exact physicalRandomDataRequest_same_rank_cost source target N P F exponent H Q tau
    (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
    (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow _ _ sourceAnswer parent.val.state answer

theorem chargedRandomGlobalQuery_earlier_cost :
    (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial (Sum.inr parent)).cost
      (Sum.elim sourceAnswer (fun child => Sum.elim (fun entry => (initial entry : ℚ))
        (fun r => answer r.val) child.val))
      (Sum.elim (fun _ => 0) (fun child => chargedEarlierWeight (Sum.inr parent) child.val)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
      (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow
      (readGroup parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩ (Fin.ofNat R (parent.val.index - T - 1)))
      (readInteger parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩ (Fin.ofNat R (parent.val.index - T - 1)))
      parent.val.state).cost
      (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim (fun _ => 0) (fun child => physicalEarlierReadWeight (T + (parent.val.index - T)) child.val)) := by
  simp only [chargedEarlierWeight_table]
  rw [chargedRandomGlobalQuery_refinement_cost source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta readGroup readInteger initial sourceAnswer answer (fun _ => 0) _ _ parent hindex hbelow hshort]
  have hrank : (PhysicalTableRequest.refinement parent.val.pass parent.val.copy parent.val.node
      T (parent.val.index - T) parent.val.state).rank T S = parent.val.rank T S := by
    unfold PhysicalTableRequest.refinement PhysicalTableRequest.rank
    dsimp only
    congr 1
    omega
  rw [← hrank]
  exact physicalRandomDataRequest_earlier_rank_cost source target N P F exponent H Q tau
    (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
    (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow _ _ sourceAnswer parent.val.state answer

end Costs

end EditApproximation

end OAI
