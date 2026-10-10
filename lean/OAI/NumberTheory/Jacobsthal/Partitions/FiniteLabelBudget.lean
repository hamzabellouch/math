import Mathlib.MeasureTheory.Measure.Real
import OAI.NumberTheory.Jacobsthal.Probability.ActualCouplingUpdates

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.FiniteLabelBudget

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelBinConditioning

section Vectors
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem total_l1_le_twice_live (a b : ι → ℝ) (c : ι)
    (ha : ∑ i,a i = 1) (hb : ∑ i,b i = 1) :
    ∑ i,|a i-b i| ≤ 2*(∑ i ∈ Finset.univ.erase c,|a i-b i|) := by
  have hsa := Finset.sum_erase_add (s:=Finset.univ) a (Finset.mem_univ c)
  have hsb := Finset.sum_erase_add (s:=Finset.univ) b (Finset.mem_univ c)
  have hsd := Finset.sum_sub_distrib (s:=Finset.univ.erase c) (f:=a) (g:=b)
  have heq : a c-b c = -(∑ i ∈ Finset.univ.erase c,(a i-b i)) := by rw [hsd]; linarith
  have hc : |a c-b c| ≤ ∑ i ∈ Finset.univ.erase c,|a i-b i| := by
    rw [heq,abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  have hse := Finset.sum_erase_add (s:=Finset.univ) (fun i => |a i-b i|) (Finset.mem_univ c)
  linarith

theorem interior_boundary_budget (a b : ι → ℝ) (c : ι) (good : ι → Prop) [DecidablePred good]
    (ha0 : ∀ i,0 ≤ a i) (hb0 : ∀ i,0 ≤ b i) (ha : ∑ i,a i = 1) (hb : ∑ i,b i = 1) :
    ∑ i,|a i-b i| ≤ 2*((∑ i ∈ (Finset.univ.erase c).filter good,|a i-b i|)+
      (∑ i ∈ (Finset.univ.erase c).filter (fun i => ¬good i),(a i+b i))) := by
  classical
  apply (total_l1_le_twice_live a b c ha hb).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hsplit := Finset.sum_filter_add_sum_filter_not (s:=Finset.univ.erase c)
    (p:=good) (f:=fun i => |a i-b i|)
  rw [← hsplit]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro i _
  rw [abs_le]
  constructor <;> linarith [ha0 i,hb0 i]
end Vectors

theorem selected_label_mass {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι]
    (K : Kernel α β) [IsMarkovKernel K] {f : β → ι} (hf : Measurable f)
    (x : α) (I : Finset ι) :
    (∑ i ∈ I,labelMass K f x i) = (K x (f ⁻¹' (I:Set ι))).toReal := by
  exact sum_measureReal_preimage_singleton I (fun i _ => hf (measurableSet_singleton i))

end NumberTheoryLean.FiniteLabelBudget


end Erdos970

end OAI
