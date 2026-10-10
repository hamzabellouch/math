import OAI.Combinatorics.EditApproximation.Geometry.LocalRandomQueryKeys
import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryCostOrder

namespace OAI

/-! Exact source-read overhead of a local refinement step. The table
reads are charged separately by the existing current/earlier budgets. -/

namespace EditApproximation

section Cost

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (q : TargetInterval target.length)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (weight : ι → ℕ)
  (hearlier : ∀ input key, key ∈ (readEarlier input).keys oracle → weight key = 0)
  (hcurrent : ∀ input key, key ∈ (readCurrent input).keys oracle → weight key = 0)

include hearlier hcurrent

omit [NeZero M] in
 theorem localOnlineSourceStepQuery_source_cost_le (draw : CellGroupDraws M F Q)
    (bound : ℕ) (hread : ∀ key range, (readInteger key range).cost oracle weight ≤ bound) :
    (localOnlineSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw q readInteger readEarlier readCurrent).cost oracle weight ≤
      (localOnlineSourceKeys N P F a parentInitial q).length * bound := by
  rw [localOnlineSourceStepQuery_cost]
  dsimp only
  have hzero (integer : ℕ → TargetInterval target.length → ℕ) :
      (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
        parentInitial child initial draw integer q readEarlier readCurrent).cost oracle weight = 0 := by
    apply FiniteQuery.cost_eq_zero_of_keys
    exact localRefinementStepQuery_keys_all source target parent N P F exponent H Q
      tau a eta kappa delta t parentInitial child initial draw integer q readEarlier readCurrent
      oracle (fun key => weight key = 0) hearlier hcurrent
  rw [hzero, Nat.add_zero]
  apply list_map_sum_le_constant
  intro key
  exact hread key _

 theorem localRandomSourceStepQuery_source_cost_le (groupBound onlineBound : ℕ)
    (hgroup : ∀ key, (readGroup key).cost oracle weight ≤ groupBound)
    (honline : ∀ key range, (readInteger key range).cost oracle weight ≤ onlineBound) :
    (localRandomSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial q readGroup readInteger readEarlier readCurrent).cost oracle weight ≤
      (groupScalarKeys M F Q (localGroupQueryKeys N F exponent a parentInitial q)).length * groupBound +
        (localOnlineSourceKeys N P F a parentInitial q).length * onlineBound := by
  unfold localRandomSourceStepQuery
  rw [FiniteQuery.cost_collect]
  exact Nat.add_le_add
    (list_map_sum_le_constant _ _ _ hgroup)
    (localOnlineSourceStepQuery_source_cost_le source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial q readInteger readEarlier readCurrent oracle weight hearlier hcurrent _
      onlineBound honline)

 theorem localRandomSourceStepQuery_source_cost_labels (labels groupBound onlineBound : ℕ)
    (hlabels : ∀ key ∈ localGroupQueryKeys N F exponent a parentInitial q,
      (groupDyadicScales M key.1 F).length ≤ labels)
    (hgroup : ∀ key, (readGroup key).cost oracle weight ≤ groupBound)
    (honline : ∀ key range, (readInteger key range).cost oracle weight ≤ onlineBound) :
    (localRandomSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial q readGroup readInteger readEarlier readCurrent).cost oracle weight ≤
      (localGroupQueryKeys N F exponent a parentInitial q).length * labels * M * groupBound +
        (dyadicQueryWindow N (parentInitial q) a F).length * onlineBound := by
  refine (localRandomSourceStepQuery_source_cost_le source target parent N P F exponent H Q
    tau a eta kappa delta t parentInitial child initial q readGroup readInteger readEarlier readCurrent
    oracle weight hearlier hcurrent groupBound onlineBound hgroup honline).trans ?_
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_right groupBound
      (groupScalarKeys_length_le M F Q labels _ hlabels)
  · rw [localOnlineSourceKeys_length]

end Cost

end EditApproximation

end OAI
