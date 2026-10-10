import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomGlobalQuery
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomSourceCost
import OAI.Combinatorics.EditApproximation.Refinement.ComputedSourceReadBudget

namespace OAI

namespace EditApproximation

 theorem computed_physicalRandomGlobalQuery_source_cost {σ α : Type*} [DecidableEq α]
    {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α)
    (N P H T S copies : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hM : M = (integerParameters N).M) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (tau eta kappa delta : ℚ) (hA : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
    (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
      GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
    (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
      (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
    (initial : PhysicalEntry M J target.length → ℕ) (sourceAnswer : σ → ℚ)
    (answer : PhysicalTableRequest M J target.length → ℚ) (weight : σ → ℕ) (bound : ℕ)
    (hgroup : ∀ pass copy node time key, (readGroup pass copy node time key).cost sourceAnswer weight ≤ bound)
    (honline : ∀ pass copy node time key range,
      (readInteger pass copy node time key range).cost sourceAnswer weight ≤ bound)
    (hpositive : ∀ pass copy node q, 0 ≤ answer (PhysicalTableRequest.warmup pass copy node 0 q))
    (request : PhysicalTableRequest M J target.length) :
    (physicalRandomGlobalQuery source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) T S copies factor multiplier tau eta kappa delta readGroup readInteger
      initial request).cost (Sum.elim sourceAnswer (fun key => answer key.val))
        (Sum.elim weight (fun _ => 0)) ≤ inputHeight N ^ 91 * bound := by
  unfold physicalRandomGlobalQuery
  by_cases ha : T < request.index ∧ request.node.1.val < J ∧
      ¬ (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1
  · rw [dite_eq_left ha, FiniteQuery.mapKeys_cost]
    let node : PhysicalInternalNode M J := ⟨request.node, ha.2.1⟩
    let time : Fin R := Fin.ofNat R (request.index - T - 1)
    have hlocal := physicalRandomDataRequest_source_cost_le source target N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) tau
      (refinementFactor (factor request.pass) (inputSmallLog N)) eta kappa delta
      request.pass request.copy T S (request.index - T) (Nat.sub_pos_of_lt ha.1)
      request.node ha.2.1 (readGroup request.pass request.copy node time)
      (readInteger request.pass request.copy node time) request.state sourceAnswer answer weight bound bound
      (hgroup request.pass request.copy node time) (honline request.pass request.copy node time)
    have hkeys := computed_source_key_budget N P hN hell hM (factor request.pass) (hA _)
      (fun r => answer (PhysicalTableRequest.warmup request.pass request.copy request.node 0 r))
      request.state (hpositive _ _ _ _)
    have hbound := hlocal.trans (show _ ≤ inputHeight N ^ 91 * bound by
      rw [← Nat.add_mul]
      exact Nat.mul_le_mul_right bound hkeys)
    convert hbound using 1
    congr 1 <;> (funext key; cases key <;> rfl)
  · rw [dite_eq_right ha]
    rw [FiniteQuery.mapRight_source_cost]
    exact Nat.zero_le _

end EditApproximation

end OAI
