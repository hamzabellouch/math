import OAI.Combinatorics.EditApproximation.Refinement.ComputedRandomTableCost
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomDataRequest

namespace OAI

namespace EditApproximation

section Physical

variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
  (N P H : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
  (hM : M = (integerParameters N).M) (hP : P = (integerParameters N).P)
  (A tau eta kappa delta : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
  (pass copy T S t : ℕ) (hT : T = (integerParameters N).T)
  (ht : 0 < t) (htime : t ≤ (integerParameters N).S)
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (readGroup : GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (q : TargetInterval target.length) (sourceAnswer : σ → ℚ)
  (answer : PhysicalTableRequest M J target.length → ℚ)
  (hw : 0 ≤ answer (PhysicalTableRequest.warmup pass copy node 0 q))

include hN hell hM hP hA hT ht htime hw

 theorem computed_physicalRandom_current_reads :
    (physicalRandomDataRequestQuery source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) tau (refinementFactor A (inputSmallLog N)) eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).cost
      (Sum.elim sourceAnswer (fun key => answer key.val))
      (Sum.elim (fun _ => 0) (fun key => physicalCurrentReadWeight (T + t) key.val)) ≤
        2 * M * inputSmallLog N ^ 256 := by
  unfold physicalRandomDataRequestQuery
  refine (computed_localRandomDataQuery_table_cost source target _ N P H T t hN hell hM hP hT
    ht htime A tau eta kappa delta hA _ _ _ _ _ q _ _ _ _ 0 0 1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  · intro r
    rw [FiniteQuery.mapKeys_cost]
    exact (physicalRefinementWarmupRead_cost_current pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r _).le
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    simpa only [Nat.mul_zero, Function.comp_def, Sum.elim_inr] using
      (physicalRefinementMassQuery_cost_current pass copy T S t ht node hbelow q input _).le
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    exact (physicalRefinementWarmupRead_cost_current pass copy T S t ht node q
      (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 _).le
  · intro key
    rw [FiniteQuery.mapKeys_cost]
    exact FiniteQuery.cost_zero _ _
  · intro key range
    rw [FiniteQuery.mapKeys_cost]
    exact FiniteQuery.cost_zero _ _
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    exact (physicalRefinementEarlierQuery_cost_current pass copy T S t node hbelow q input _).le
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    exact (physicalRefinementCurrentQuery_cost_current pass copy T S t node hbelow q input _).le
  · exact hw
  · simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add]
    exact le_rfl

 theorem computed_physicalRandom_earlier_reads :
    (physicalRandomDataRequestQuery source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) tau (refinementFactor A (inputSmallLog N)) eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).cost
      (Sum.elim sourceAnswer (fun key => answer key.val))
      (Sum.elim (fun _ => 0) (fun key => physicalEarlierReadWeight (T + t) key.val)) ≤
        inputHeight N ^ (257 * (coarseExponent (inputSmallLog N) + 1)) := by
  unfold physicalRandomDataRequestQuery
  refine (computed_localRandomDataQuery_table_cost source target _ N P H T t hN hell hM hP hT
    ht htime A tau eta kappa delta hA _ _ _ _ _ q _ _ _ _ 1 1 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  · intro r
    rw [FiniteQuery.mapKeys_cost]
    exact (physicalRefinementWarmupRead_cost_earlier pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r _).le
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    simpa only [Nat.mul_one, Function.comp_def, Sum.elim_inr] using
      (physicalRefinementMassQuery_cost_earlier pass copy T S t ht node hbelow q input _).le
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    exact (physicalRefinementWarmupRead_cost_earlier pass copy T S t ht node q
      (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 _).le
  · intro key
    rw [FiniteQuery.mapKeys_cost]
    exact FiniteQuery.cost_zero _ _
  · intro key range
    rw [FiniteQuery.mapKeys_cost]
    exact FiniteQuery.cost_zero _ _
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    exact physicalRefinementEarlierQuery_cost_earlier pass copy T S t node hbelow q input _
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    exact (physicalRefinementCurrentQuery_cost_earlier pass copy T S t node hbelow q input _).le
  · exact hw
  · simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero]
    let B := inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1))
    have hH : 64 ≤ inputHeight N :=
      (by omega : 64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
    have hB : 1 ≤ B := one_le_pow₀ (by omega)
    change 2 + 2 * B + B ≤ _
    calc
      _ ≤ 5 * B := by omega
      _ ≤ inputHeight N * B := Nat.mul_le_mul_right B (by omega)
      _ = inputHeight N ^ (1 + 256 * (coarseExponent (inputSmallLog N) + 1)) := by
        dsimp only [B]
        rw [pow_add, pow_one]
      _ ≤ _ := pow_le_pow_right₀ (by omega) (by omega)

end Physical

end EditApproximation

end OAI
