import OAI.NumberTheory.Jacobsthal.Paths.CanonicalPairVisitCompletion

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.KernelPotential

noncomputable def regenerationInput : Kernel OddCost OddCost := stateFilter returnSet_measurable
noncomputable def nonregenerationInput : Kernel OddCost OddCost := stateFilter returnSet_measurable.compl

instance regenerationInput_isFiniteKernel : IsFiniteKernel regenerationInput := by unfold regenerationInput; infer_instance
instance nonregenerationInput_isFiniteKernel : IsFiniteKernel nonregenerationInput := by unfold nonregenerationInput; infer_instance

lemma regenerationInput_after_pair : regenerationInput ∘ₖ pairedCostKernel=costCaptured := by
  rw [regenerationInput,stateFilter_output]
  rfl

lemma nonregenerationInput_after_pair : nonregenerationInput ∘ₖ pairedCostKernel=costKilled := by
  rw [nonregenerationInput,stateFilter_output]
  rfl

lemma returnLaw_potential : returnLaw=potential costCaptured costKilled := rfl

lemma hitOrReturn_input_split : hitOrReturn=regenerationInput+returnLaw ∘ₖ nonregenerationInput := by
  ext z S hS
  rw [hitOrReturn,Kernel.piecewise_apply,_root_.add_apply,Measure.add_apply,
    regenerationInput,stateFilter_apply,nonregenerationInput,stateFilter_input]
  by_cases hz : z ∈ returnSet
  · simp only [hz,ite_true,mem_compl_iff,not_true_eq_false,ite_false,Measure.coe_zero,Pi.zero_apply,add_zero]
    rfl
  · simp only [hz,ite_false,mem_compl_iff,not_false_eq_true,ite_true,Measure.coe_zero,Pi.zero_apply,zero_add]

theorem hitOrReturn_eq_input_potential :
    hitOrReturn=potential regenerationInput (pairedCostKernel ∘ₖ nonregenerationInput) := by
  have hR : returnLaw=
      (potential regenerationInput (pairedCostKernel ∘ₖ nonregenerationInput)) ∘ₖ pairedCostKernel := by
    rw [returnLaw_potential,← regenerationInput_after_pair,← nonregenerationInput_after_pair]
    exact potential_exchange regenerationInput pairedCostKernel nonregenerationInput
  rw [potential_unfold,← Kernel.comp_assoc,← hR]
  exact hitOrReturn_input_split

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
