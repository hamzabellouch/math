import OAI.NumberTheory.Ostmann.Characters.TemplateActualPivotFactors
import OAI.NumberTheory.Ostmann.Characters.TemplateBranchPhase
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryConstituent

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem scheduledInput_surviving_entry (k j:ℕ) (hj:j<k) (width:Role→ℕ)
    (i h:SurvivingPrimeIndex k j width) :
    constituentGraph k j width (scheduledConstituentInput k j hj width (.inr i))
      (scheduledConstituentInput k j hj width (.inr h)) =
    collapsedConstituentGraph (schedule k j) j width (pivotSlot k j hj)
      (graph k j) (intraGraph k j) (some i) (some h) := by
  cases i <;> cases h <;> rfl

def actualBranchUnary (k j:ℕ) (hj:j<k) (width:Role→ℕ)
    (p:UnaryOutputIndex k j width→ℕ) [∀i,Fact (p i).Prime]
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (side:Bool) (v:ℤ) (t:HistoryReconstruction.Tree j)
    (i:SurvivingPrimeIndex k j width) : ℂ :=
  actualHistoryUnary k width (χ (survivingBranchIndex side i)) j v t
    (scheduledConstituentInput k j hj width (.inr i))

theorem actualPivotSurviving_branch (k j:ℕ) (hj:j<k) (width:Role→ℕ)
    (p:UnaryOutputIndex k j width→ℕ) [∀i,Fact (p i).Prime]
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (a:∀i,ZMod (p i))
    (side:Bool) (P:ℕ) (v:ℤ) (t:HistoryReconstruction.Tree j) :
    actualPivotSurviving k j hj width (fun i => p (survivingBranchIndex side i))
      (fun i => χ (survivingBranchIndex side i)) (fun i => a (survivingBranchIndex side i)) P v t =
    branchSurvivingPhase p χ a
      (collapsedConstituentGraph (schedule k j) j width (pivotSlot k j hj)
        (graph k j) (intraGraph k j))
      (actualBranchUnary k j hj width p χ side v t) P v side := by
  simp only [actualPivotSurviving,branchSurvivingPhase,actualBranchUnary,scheduledInput_surviving_entry]

theorem actualPivotSurviving_rows (k j:ℕ) (hj:j<k) (width:Role→ℕ)
    (p:UnaryOutputIndex k j width→ℕ) [∀i,Fact (p i).Prime]
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (hχ:∀i,χ i≠1) (a:∀i,ZMod (p i))
    (P:ℕ) (s:ℤ) (t:HistoryReconstruction.Tree (j+1))
    (ht:∀i,HistoryFrequencyUnits (p i) (j+1) s t) (side:Bool) :
    let b := collapsedConstituentGraph (schedule k j) j width (pivotSlot k j hj)
      (graph k j) (intraGraph k j)
    let ν := historyCopiedUnaryUnits k j width p χ hχ s t ht
    let ξ := historyOutsideUnaryUnits k j width p χ hχ s t ht
    actualPivotSurviving k j hj width (fun i => p (survivingBranchIndex side i))
      (fun i => χ (survivingBranchIndex side i)) (fun i => a (survivingBranchIndex side i))
      P (unaryChildFrequency t side) (unaryChildTree t side) =
    ((∏i,branchCopiedTranslation p a (P:ℤ) (unaryChildFrequency t side) side i)*
      (∏i,outsideTranslation p a (P:ℤ) (unaryChildFrequency t side) side i))*
    ((∏i,(ν (i,side):ℂ)*oldPrimeCopiedRow p i side (χ (.inl (i,side))) b (P:ℤ))*
      (∏i,(ξ i side:ℂ)*oldPrimeSharedRow p i side (χ (.inr i)) b (P:ℤ))) := by
  dsimp only
  rw [actualPivotSurviving_branch,branchSurvivingPhase_rows]
  simp only [actualBranchUnary,survivingBranchIndex,historyCopiedUnaryUnits,historyOutsideUnaryUnits,
    actualHistoryUnaryUnit_coe,scheduledConstituentInput,constituentInputEquiv_copied,
    constituentInputEquiv_outside]

end Ostmann.Characters.Template

end

end OAI
