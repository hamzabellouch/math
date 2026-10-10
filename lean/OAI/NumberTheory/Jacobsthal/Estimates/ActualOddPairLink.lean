import OAI.NumberTheory.Jacobsthal.Renewal.OddPairCycleGrouping

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.CostReturnLaw

noncomputable def oddGoodInput (v H : ℝ) : Set OddCost := returnSet ∩ ordinaryCostWindow v H

lemma oddGoodInput_embed (v H : ℝ) (z : OddCost) :
    embedOdd z ∈ regenerativeCostWindow v H ↔ z ∈ oddGoodInput v H := Iff.rfl

lemma pairWindowContinue_apply (v H : ℝ) (z : OddCost) :
    pairWindowContinue v H z=if z ∈ ordinaryCostWindow v H then pairBranchKernel false z else pairedCostKernel z := by
  rw [pairWindowContinue,_root_.add_apply,stateFilter_input]
  by_cases hz : z ∈ ordinaryCostWindow v H
  · simp [hz]
  · simp only [hz,ite_false,mem_compl_iff,not_false_eq_true,ite_true]
    have he := congrArg (fun K : Kernel OddCost OddCost => K z) pairBranch_sum
    rw [_root_.add_apply] at he
    simpa only [add_comm] using he

lemma oddConsecutiveContinue_apply (v H : ℝ) (z : OddCost) :
    oddConsecutiveContinue v H z=if z ∈ oddGoodInput v H then pairBranchKernel false z else pairedCostKernel z := by
  rw [oddConsecutiveContinue,_root_.add_apply,nonregenerationInput,stateFilter_input,regenerationInput,stateFilter_input]
  by_cases hr : z ∈ returnSet
  · simp only [hr,ite_true,mem_compl_iff,not_true_eq_false,ite_false,zero_add]
    rw [pairWindowContinue_apply]
    simp only [oddGoodInput,mem_inter_iff,hr,true_and]
  · simp only [hr,ite_false,mem_compl_iff,not_false_eq_true,ite_true,add_zero]
    simp only [oddGoodInput,mem_inter_iff,hr,false_and,ite_false]

lemma consecutiveContinue_apply (v H : ℝ) (s : CostState) :
    consecutiveContinue v H s=if s ∈ regenerativeCostWindow v H then
      (costKernel ∘ₖ costKernel.restrict markedArrival_measurable.compl) s else (costKernel^2) s := by
  ext S hS
  rw [consecutiveContinue,Kernel.comp_apply' _ _ _ hS,consecutiveFirstContinue,Kernel.piecewise_apply]
  by_cases hs : s ∈ regenerativeCostWindow v H
  · rw [ite_eq_left hs,ite_eq_left hs,Kernel.comp_apply' _ _ _ hS]
  · rw [ite_eq_right hs,ite_eq_right hs,pow_two]
    exact (Kernel.comp_apply' costKernel costKernel s hS).symm

lemma false_arrival_restriction :
    costKernel.restrict (firstArrivalMark_measurable (measurableSet_singleton false))=
      costKernel.restrict markedArrival_measurable.compl := by
  ext s S hS
  rw [Kernel.restrict_apply' _ _ _ hS,Kernel.restrict_apply' _ _ _ hS]
  change costKernel s (S ∩ {y | firstArrivalMark y=false})=costKernel s (S ∩ markedArrivalᶜ)
  rw [false_arrival_set]

theorem oddConsecutiveContinue_embed (v H : ℝ) (z : OddCost) :
    (oddConsecutiveContinue v H z).map embedOdd=consecutiveContinue v H (embedOdd z) := by
  rw [oddConsecutiveContinue_apply,consecutiveContinue_apply]
  by_cases hz : z ∈ oddGoodInput v H
  · rw [ite_eq_left hz,ite_eq_left ((oddGoodInput_embed v H z).mpr hz),pairBranch_full_projection,false_arrival_restriction]
  · rw [ite_eq_right hz,ite_eq_right (fun h => hz ((oddGoodInput_embed v H z).mp h))]
    exact pairedCost_full_grouping z

lemma oddConsecutiveCapture_mass (v H : ℝ) (z : OddCost) :
    oddConsecutiveCapture v H z univ=if z ∈ oddGoodInput v H then nextMarkWeight z else 0 := by
  rw [oddConsecutiveCapture,regenerationInput,stateFilter_input]
  by_cases hr : z ∈ returnSet
  · rw [ite_eq_left hr,ordinaryWindowCapture_mass]
    simp only [oddGoodInput,mem_inter_iff,hr,true_and]
  · rw [ite_eq_right hr]
    simp [oddGoodInput,hr]

lemma consecutiveCapture_mass (v H : ℝ) (s : CostState) :
    consecutiveCapture v H s univ=if s ∈ regenerativeCostWindow v H then costKernel s markedArrival else 0 := by
  rw [consecutiveCapture,stateFilter_input]
  split_ifs
  · rw [Kernel.restrict_apply' _ _ _ MeasurableSet.univ,univ_inter]
  · rfl

theorem oddConsecutiveCapture_mass_embed (v H : ℝ) (z : OddCost) :
    oddConsecutiveCapture v H z univ=consecutiveCapture v H (embedOdd z) univ := by
  rw [oddConsecutiveCapture_mass,consecutiveCapture_mass]
  by_cases hz : z ∈ oddGoodInput v H
  · rw [ite_eq_left hz,ite_eq_left ((oddGoodInput_embed v H z).mpr hz),nextMarkWeight_pair_mass,pairBranch_marked_first_mass]
  · rw [ite_eq_right hz,ite_eq_right (fun h => hz ((oddGoodInput_embed v H z).mp h))]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
