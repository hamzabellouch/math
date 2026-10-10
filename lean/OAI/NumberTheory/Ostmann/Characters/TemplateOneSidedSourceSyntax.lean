import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateTotalCountActual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingExpressionsSource
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurvivingOrigins

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedSourceSyntax
open SymbolicHistory Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale DiagonalEstimate TemplateOneSidedBudget TemplateOneSidedSupportSurviving
attribute [local instance] Classical.propDecidable

def sourceCellConstant (k : ℕ) : ℕ := ⌈maxCells 4 k⌉₊
def sourceWidthConstant (k : ℕ) : ℕ := 1+sourceCellConstant k
def sourceCopiedConstant (k : ℕ) : ℕ := 2^k*(1+2*sourceCellConstant k)
def sourceExpressionConstant (k : ℕ) : ℕ := 2*(sourceWidthConstant k+1)
def sourceRatioConstant (k : ℕ) : ℕ := 2*(sourceCopiedConstant k+1)
def sourceSurvivingSlotConstant (k : ℕ) : ℕ :=
  1+∑j : Fin (k+1),Fintype.card (SurvivingSlot k j.val)
def sourceSurvivingConstant (k : ℕ) : ℕ := sourceSurvivingSlotConstant k*sourceWidthConstant k

theorem sourceWidthConstant_pos (k : ℕ) : 0<sourceWidthConstant k := by
  unfold sourceWidthConstant
  omega

theorem sourceCopiedConstant_pos (k : ℕ) : 0<sourceCopiedConstant k := by
  unfold sourceCopiedConstant
  positivity

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)

theorem actual_sourceCell_bound : configCellCount w.configuration ≤ sourceCellConstant k := by
  have hh := (fixedConfiguration_cell_count w).trans (Nat.le_ceil (maxCells 4 k))
  exact_mod_cast hh

theorem actual_survivingSourceWidthBudget :
    survivingSourceWidthBudget w.configuration ≤ sourceWidthConstant k := by
  have hh := actual_sourceCell_bound w
  rw [configCellCount_eq] at hh
  unfold survivingSourceWidthBudget sourceWidthConstant
  omega

theorem actual_sourceWidth_le (m : ℕ) (r : Role) :
    sourceWidth w.configuration m r ≤ sourceWidthConstant k*(m+1) :=
  (sourceWidth_le_surviving_budget w.configuration m r).trans
    (Nat.mul_le_mul_right (m+1) (actual_survivingSourceWidthBudget w))

theorem actual_sourceCopied_card_le (m j : ℕ) (hj : j ≤ k) :
    Fintype.card (ActualCopied w.configuration m j) ≤ sourceCopiedConstant k*(m+1) := by
  have hh := actual_sourceCell_bound w
  have hsize : m+1+2*configCellCount w.configuration ≤ (1+2*sourceCellConstant k)*(m+1) := by
    nlinarith
  have hp : (2:ℕ)^j ≤ 2^k := Nat.pow_le_pow_right (by omega) hj
  calc
    _  ≤  2^j*(m+1+2*configCellCount w.configuration) := actualCopied_card_le w.configuration m j
    _  ≤  2^k*((1+2*sourceCellConstant k)*(m+1)) := Nat.mul_le_mul hp hsize
    _ = _ := by unfold sourceCopiedConstant; rw [Nat.mul_assoc]

theorem actual_sourceSurviving_card_le (m j : ℕ) (hj : j ≤ k) :
    Fintype.card (Σi : SurvivingSlot k j,
      Fin (survivingWidth k j (sourceWidth w.configuration m) i)) ≤
        sourceSurvivingConstant k*(m+1) := by
  have hwidth (i : SurvivingSlot k j) :
      survivingWidth k j (sourceWidth w.configuration m) i ≤ sourceWidthConstant k*(m+1) := by
    cases i <;> exact actual_sourceWidth_le w m _
  have hc : Fintype.card (SurvivingSlot k j) ≤ sourceSurvivingSlotConstant k := by
    have hh := Finset.single_le_sum (f:=fun q : Fin (k+1) => Fintype.card (SurvivingSlot k q.val))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨j,by omega⟩ : Fin (k+1)))
    unfold sourceSurvivingSlotConstant
    exact hh.trans (Nat.le_add_left _ _)
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∑_i : SurvivingSlot k j,sourceWidthConstant k*(m+1) :=
      Finset.sum_le_sum (fun i _ => hwidth i)
    _ = Fintype.card (SurvivingSlot k j)*(sourceWidthConstant k*(m+1)) := by simp
    _ ≤ sourceSurvivingSlotConstant k*(sourceWidthConstant k*(m+1)) :=
      Nat.mul_le_mul_right _ hc
    _ = _ := by unfold sourceSurvivingConstant; rw [Nat.mul_assoc]

theorem actual_survivingSampledExpressions_syntaxSize (m j : ℕ) (P : ℤ)
    (e : Equiv.Perm (ActualCopied w.configuration m j)) (i : (schedule k j).Slot) :
    (survivingSampledExpressions k j (sourceWidth w.configuration m) P e i).syntaxSize ≤ 
      sourceExpressionConstant k*(m+1) :=
  survivingSampledExpressions_syntaxSize_linear k j (sourceWidth w.configuration m) P e
    (sourceWidthConstant k) m (actual_sourceWidth_le w m) i

theorem actual_survivingCopiedProductExpression_syntaxSize (m j : ℕ) (hj : j ≤ k) :
    (survivingCopiedProductExpression k j (sourceWidth w.configuration m)).syntaxSize ≤ 
      sourceRatioConstant k*(m+1) := by
  apply (survivingCopiedProductExpression_syntaxSize k j (sourceWidth w.configuration m)).trans
  have hh := actual_sourceCopied_card_le w m j hj
  unfold sourceRatioConstant
  change Fintype.card (ActualCopied w.configuration m j) ≤ _ at hh
  nlinarith

end
end Ostmann.Characters.TemplateOneSidedSourceSyntax

end

end OAI
