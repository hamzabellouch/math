import OAI.Combinatorics.EditApproximation.Refinement.ComputedGlobalSourceCost
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomCost
import OAI.Combinatorics.EditApproximation.Geometry.ChargedTerminalCost

namespace OAI

namespace EditApproximation

section Cost

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ) (weight : σ → ℕ) (bound : ℕ)
  (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hM : M = (integerParameters N).M)
  (hA : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
  (hgroup : ∀ pass copy node time key, (readGroup pass copy node time key).cost sourceAnswer weight ≤ bound)
  (honline : ∀ pass copy node time key range,
    (readInteger pass copy node time key range).cost sourceAnswer weight ≤ bound)

local notation "tableValue" => localRequestValue source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S copies factor multiplier
    tau eta kappa delta group integer initial

include hN hell hM hA hgroup honline in
 theorem computed_chargedRandomGlobalQuery_source_cost
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomGlobalQuery source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
      readGroup readInteger initial request).cost
      (Sum.elim sourceAnswer (fun child => chargedRequestValue source target N P (inputSmallLog N)
        (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
          tau eta kappa delta group integer initial child.val))
      (Sum.elim weight (fun _ => 0)) ≤ inputHeight N ^ 91 * bound := by
  cases request with
  | inl entry => exact Nat.zero_le _
  | inr parent =>
    by_cases hi : parent.val.index ≤ T
    · unfold chargedRandomGlobalQuery
      dsimp only
      rw [ite_eq_left hi, FiniteQuery.mapKeys_cost]
      simp only [Function.comp_def, Sum.elim_inr]
      rw [FiniteQuery.cost_zero]
      exact Nat.zero_le _
    · by_cases hb : parent.val.node.1.val < J
      · by_cases hs : (physicalSourceInterval source.length parent.val.node).hi -
            (physicalSourceInterval source.length parent.val.node).lo ≤ 1
        · unfold chargedRandomGlobalQuery
          dsimp only
          rw [ite_eq_right hi, ite_eq_left hb, ite_eq_left hs, FiniteQuery.mapKeys_cost]
          simp only [Function.comp_def, Sum.elim_inr]
          rw [FiniteQuery.cost_zero]
          exact Nat.zero_le _
        · have hanswer : chargedRequestValue source target N P (inputSmallLog N)
              (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
              tau eta kappa delta group integer initial =
              Sum.elim (fun entry => (initial entry : ℚ)) (fun r => tableValue r.val) := by
            funext key
            cases key <;> rfl
          have hz : (fun _ : ChargedPhysicalRequest M J target.length passes copies T S => 0) =
              chargedTableWeight 0 (fun _ => 0) := by
            funext key
            cases key <;> rfl
          rw [hanswer]
          have hcost := chargedRandomGlobalQuery_refinement_cost source target N P (inputSmallLog N)
            (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
            tau eta kappa delta readGroup readInteger initial sourceAnswer tableValue weight 0 (fun _ => 0)
            parent (by omega) hb hs
          simp only [← hz] at hcost
          rw [hcost]
          rw [← physicalRandomGlobalQuery_refinement_cost source target N P (inputSmallLog N)
            (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S copies factor multiplier
            tau eta kappa delta readGroup readInteger initial sourceAnswer tableValue weight (fun _ => 0)
            parent.val (by omega) hb hs]
          apply computed_physicalRandomGlobalQuery_source_cost source target N P H T S copies
            hN hell hM factor multiplier tau eta kappa delta hA readGroup readInteger initial
            sourceAnswer tableValue weight bound hgroup honline
          intro pass copy node q
          rw [localRequestValue_initial]
          exact stageInitial_nonneg_all_seeds _ _ _ _ _ _ _ _
      · unfold chargedRandomGlobalQuery
        dsimp only
        rw [ite_eq_right hi, ite_eq_right hb, FiniteQuery.mapKeys_cost]
        simp only [Function.comp_def, Sum.elim_inr]
        rw [FiniteQuery.cost_zero]
        exact Nat.zero_le _

end Cost

end EditApproximation

end OAI
