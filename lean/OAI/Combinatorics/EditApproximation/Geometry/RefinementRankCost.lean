import OAI.Combinatorics.EditApproximation.Geometry.GlobalQueryCost

namespace OAI

/-! For a fixed pass, the physical rank partition equals the concrete
warmup/refinement index partition on every emitted data-query key. -/

namespace EditApproximation

section Costs

variable {α : Type*} (source target : List α) {M J : ℕ}
  (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
  (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length) (answer : PhysicalTableRequest M J target.length → ℚ)

theorem physicalRefinementDataRequest_same_rank_cost :
    (physicalRefinementDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow draw integer q).cost (fun child => answer child.val)
      (fun child => if ¬ child.val.rank T S <
        (PhysicalTableRequest.refinement pass copy node T t q).rank T S then 1 else 0) =
    (physicalRefinementDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow draw integer q).cost (fun child => answer child.val)
      (fun child => physicalCurrentReadWeight (T + t) child.val) := by
  apply FiniteQuery.cost_congr_weights
  intro key hk
  have hkey := physicalRefinementDataRequest_keys_pass_copy source target N P F exponent H Q
    tau a eta kappa delta pass copy T S t ht node hbelow draw integer q _ key hk
  have heq := PhysicalTableRequest.rank_not_lt_iff_index_eq_of_pass T S
    (PhysicalTableRequest.refinement pass copy node T t q) key.val hkey.1 hkey.2.2
  by_cases hi : key.val.index = T + t
  · have hr := heq.mpr hi
    simp only [ite_eq_left hr, physicalCurrentReadWeight, ite_eq_left hi]
  · have hr : ¬ ¬ key.val.rank T S <
        (PhysicalTableRequest.refinement pass copy node T t q).rank T S := fun h => hi (heq.mp h)
    simp only [ite_eq_right hr, physicalCurrentReadWeight, ite_eq_right hi]

theorem physicalRefinementDataRequest_earlier_rank_cost :
    (physicalRefinementDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow draw integer q).cost (fun child => answer child.val)
      (fun child => if child.val.rank T S <
        (PhysicalTableRequest.refinement pass copy node T t q).rank T S then 1 else 0) =
    (physicalRefinementDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow draw integer q).cost (fun child => answer child.val)
      (fun child => physicalEarlierReadWeight (T + t) child.val) := by
  apply FiniteQuery.cost_congr_weights
  intro key hk
  have hkey := physicalRefinementDataRequest_keys_pass_copy source target N P F exponent H Q
    tau a eta kappa delta pass copy T S t ht node hbelow draw integer q _ key hk
  have heq := PhysicalTableRequest.rank_lt_iff_index_lt_of_pass T S
    (PhysicalTableRequest.refinement pass copy node T t q) key.val hkey.1
  by_cases hi : key.val.index < T + t
  · have hr := heq.mpr hi
    simp only [ite_eq_left hr, physicalEarlierReadWeight, ite_eq_left hi]
  · have hr : ¬ key.val.rank T S <
        (PhysicalTableRequest.refinement pass copy node T t q).rank T S := fun h => hi (heq.mp h)
    simp only [ite_eq_right hr, physicalEarlierReadWeight, ite_eq_right hi]

end Costs

end EditApproximation

end OAI
