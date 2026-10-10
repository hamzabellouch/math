import OAI.Combinatorics.EditApproximation.Geometry.ChargedTerminalCost
import OAI.Combinatorics.EditApproximation.Refinement.ComputedRandomPhysicalCost
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomIndexCost
import OAI.Combinatorics.EditApproximation.Refinement.ComputedWarmupReadBudget

namespace OAI

/-! Uniform edge budgets for the actual charged global interpreter.
The bounds hold for every initial seed and every draw, including failed
approximation events. -/

namespace EditApproximation

section Current

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

variable
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)

local notation "values" => localRequestValue source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S copies factor multiplier
    tau eta kappa delta group integer initial

variable (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
  (hM : M = (integerParameters N).M)
  (hAmax : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
  (hP : P = (integerParameters N).P) (hT : T = (integerParameters N).T)
  (hS : S = (integerParameters N).S)

include hN hell hM hAmax hP hT hS in
 theorem computed_chargedRandomGlobalQuery_current_reads
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomGlobalQuery source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
      readGroup readInteger initial request).cost
      (Sum.elim sourceAnswer (fun child => chargedRequestValue source target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
        group integer initial child.val))
      (Sum.elim (fun _ => 0) (fun child => chargedSameWeight request child.val)) ≤ 2 * M * inputSmallLog N ^ 256 := by
  cases request with
  | inl entry => exact Nat.zero_le _
  | inr parent =>
    by_cases hi : parent.val.index ≤ T
    · unfold chargedRandomGlobalQuery
      dsimp only
      rw [ite_eq_left hi, FiniteQuery.mapKeys_cost]
      simp only [Function.comp_def, Sum.elim_inr]
      rw [chargedWarmupQuery_same_cost_zero]
      exact Nat.zero_le _
    · by_cases hb : parent.val.node.1.val < J
      · by_cases hs : (physicalSourceInterval source.length parent.val.node).hi -
            (physicalSourceInterval source.length parent.val.node).lo ≤ 1
        · unfold chargedRandomGlobalQuery
          dsimp only
          rw [ite_eq_right hi, ite_eq_left hb, ite_eq_left hs, FiniteQuery.mapKeys_cost]
          simp only [Function.comp_def, Sum.elim_inr]
          rw [chargedInitialQuery_same_cost_zero]
          exact Nat.zero_le _
        · have hanswer : chargedRequestValue source target N P (inputSmallLog N)
              (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
              tau eta kappa delta group integer initial =
              Sum.elim (fun entry => (initial entry : ℚ)) (fun r => values r.val) := by
            funext key
            cases key <;> rfl
          rw [hanswer]
          rw [chargedRandomGlobalQuery_current_cost source target N P (inputSmallLog N)
            (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
            tau eta kappa delta readGroup readInteger sourceAnswer values initial parent (by omega) hb hs]
          apply computed_physicalRandom_current_reads source target N P H hN hell hM hP
            (factor parent.val.pass) tau eta kappa delta (hAmax _) parent.val.pass parent.val.copy
            T S (parent.val.index - T) hT (by omega)
            (by have hi := parent.property.2.2; omega) parent.val.node hb
          rw [localRequestValue_initial]
          exact stageInitial_nonneg_all_seeds _ _ _ _ _ _ _ _
      · unfold chargedRandomGlobalQuery
        dsimp only
        rw [ite_eq_right hi, ite_eq_right hb, FiniteQuery.mapKeys_cost]
        simp only [Function.comp_def, Sum.elim_inr]
        rw [chargedInitialQuery_same_cost_zero]
        exact Nat.zero_le _


variable (hcopies : copies ≤ inputHeight N ^ 2)
  (hAmin : ∀ pass, 1 ≤ factor pass)

include hN hell hM hAmax hP hT hS hcopies hAmin in
 theorem computed_chargedRandomGlobalQuery_earlier_reads
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomGlobalQuery source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
      readGroup readInteger initial request).cost
      (Sum.elim sourceAnswer (fun child => chargedRequestValue source target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
        group integer initial child.val))
      (Sum.elim (fun _ => 0) (fun child => chargedEarlierWeight request child.val)) ≤
        inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1)) := by
  cases request with
  | inl entry => exact Nat.zero_le _
  | inr parent =>
    let oracle := fun child : {child : ChargedPhysicalRequest M J target.length passes copies T S //
        child.rank < ChargedPhysicalRequest.rank (Sum.inr parent)} =>
      chargedRequestValue source target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
        group integer initial child.val
    have hmono (program : FiniteQuery {child : ChargedPhysicalRequest M J target.length passes copies T S //
        child.rank < ChargedPhysicalRequest.rank (Sum.inr parent)}) :
        program.cost oracle (fun child => chargedEarlierWeight (Sum.inr parent) child.val) ≤
          program.cost oracle (fun _ => 1) := by
      apply FiniteQuery.cost_mono_weights
      intro child
      unfold chargedEarlierWeight
      split_ifs <;> omega
    by_cases hi : parent.val.index ≤ T
    · unfold chargedRandomGlobalQuery
      dsimp only
      rw [ite_eq_left hi, FiniteQuery.mapKeys_cost]
      simp only [Function.comp_def, Sum.elim_inr]
      exact (hmono _).trans (computed_chargedWarmupQuery_reads source target N P hN hell hM hP hcopies
        factor multiplier parent oracle (hAmin _) (hAmax _))
    · by_cases hb : parent.val.node.1.val < J
      · by_cases hs : (physicalSourceInterval source.length parent.val.node).hi -
            (physicalSourceInterval source.length parent.val.node).lo ≤ 1
        · unfold chargedRandomGlobalQuery
          dsimp only
          rw [ite_eq_right hi, ite_eq_left hb, ite_eq_left hs, FiniteQuery.mapKeys_cost]
          simp only [Function.comp_def, Sum.elim_inr]
          exact (hmono _).trans (computed_chargedInitialQuery_reads source target N P hN hell hM hP hcopies
            factor multiplier parent oracle (hAmin _) (hAmax _))
        · have hanswer : chargedRequestValue source target N P (inputSmallLog N)
              (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
              tau eta kappa delta group integer initial =
              Sum.elim (fun entry => (initial entry : ℚ)) (fun r => values r.val) := by
            funext key
            cases key <;> rfl
          rw [hanswer]
          rw [chargedRandomGlobalQuery_earlier_cost source target N P (inputSmallLog N)
            (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
            tau eta kappa delta readGroup readInteger sourceAnswer values initial parent (by omega) hb hs]
          calc
            _ ≤ inputHeight N ^ (257 * (coarseExponent (inputSmallLog N) + 1)) := by
              apply computed_physicalRandom_earlier_reads source target N P H hN hell hM hP
                (factor parent.val.pass) tau eta kappa delta (hAmax _) parent.val.pass parent.val.copy
                T S (parent.val.index - T) hT (by omega)
                (by
                  have h := parent.property.2.2
                  have htime : parent.val.index - T ≤ S := by omega
                  exact htime.trans_eq hS) parent.val.node hb
              rw [localRequestValue_initial]
              exact stageInitial_nonneg_all_seeds _ _ _ _ _ _ _ _
            _ ≤ _ := pow_le_pow_right₀ (Nat.one_le_two_pow) (by omega)
      · unfold chargedRandomGlobalQuery
        dsimp only
        rw [ite_eq_right hi, ite_eq_right hb, FiniteQuery.mapKeys_cost]
        simp only [Function.comp_def, Sum.elim_inr]
        exact (hmono _).trans (computed_chargedInitialQuery_reads source target N P hN hell hM hP hcopies
          factor multiplier parent oracle (hAmin _) (hAmax _))

end Current

end EditApproximation

end OAI
