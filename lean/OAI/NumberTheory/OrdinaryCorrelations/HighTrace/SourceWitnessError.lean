import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeSplit
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.NumericalLine
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CylinderBudget

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.SourceCylinder OrdinaryCorrelations.FiniteIntegration
open Finset Classical Filter

namespace NumericalLine

noncomputable def sourceWitnessError {B τ C₀ T : ℝ} (D : (sourceSystem B).DivisorFamily B τ C₀)
    {h : ℕ} (hh : 0 < h) (K₀ : ℝ) (cut : (sourceSystem B).Cutoffs T) : ℝ :=
  cylinderBudget (sourceListSlotBudget C₀ B) *
    ∑ w : NumericalLine D h (sourceLength B),
      residualWitnessIntegral (D:=D) (L:=pathLength B) w.line cut (sourceRetained hh K₀ w) (listCutoff B)

noncomputable def sourceAllowedRetainedSum {B τ C₀ T : ℝ} (D : (sourceSystem B).DivisorFamily B τ C₀)
    {h : ℕ} (hh : 0 < h) (K₀ : ℝ) (cut : (sourceSystem B).Cutoffs T) : ℝ :=
  ∑ w : NumericalLine D h (sourceLength B),
    retainedAllowedIntegral (D:=D) (L:=pathLength B) w.line cut (sourceRetained hh K₀ w)

lemma listCutoff_pos {B : ℝ} (hB : 1 ≤ B) : 1 ≤ listCutoff B := by
  have hh : (1:ℝ) ≤ B^(4*epsilon) := Real.one_le_rpow hB (by norm_num [epsilon])
  have hc := hh.trans (Nat.le_ceil (B^(4*epsilon)))
  exact_mod_cast hc

lemma source_line_cylinder_reduction {B τ C₀ T K₀ : ℝ}
    {D : (sourceSystem B).DivisorFamily B τ C₀} {h : ℕ} (hh : 0 < h)
    (hB : 1 ≤ B) (cut : (sourceSystem B).Cutoffs T) (w : NumericalLine D h (sourceLength B)) :
    retainedAllowedIntegral (D:=D) (L:=pathLength B) w.line cut (sourceRetained hh K₀ w) ≤
      cylinderBudget (sourceListSlotBudget C₀ B) *
        (∑ l ∈ boundedLists (AttachedSpec w.line D (pathLength B)) (listCutoff B),
          assignedKernelIntegral w.line cut l (sourceRetained hh K₀ w)) +
      cylinderBudget (sourceListSlotBudget C₀ B) *
        residualWitnessIntegral (D:=D) (L:=pathLength B) w.line cut
          (sourceRetained hh K₀ w) (listCutoff B) := by
  have hp := primitive_cylinder_reduction w.line cut (sourceRetained hh K₀ w)
    (fun a ha => ha.2) (listCutoff B) (listCutoff_pos hB)
  refine hp.trans (add_le_add ?_ le_rfl)
  apply mul_le_mul_of_nonneg_right (coefficient_le_cylinderBudget (sourceListSlotBudget C₀ B))
  exact sum_nonneg (fun l hl => LineList.assignedKernelIntegral_nonneg w.line cut l (sourceRetained hh K₀ w))

lemma source_allowed_retained_reduction {B τ C₀ T K₀ : ℝ}
    (D : (sourceSystem B).DivisorFamily B τ C₀) {h : ℕ} (hh : 0 < h)
    (hB : 1 ≤ B) (cut : (sourceSystem B).Cutoffs T) :
    sourceAllowedRetainedSum D hh K₀ cut ≤
      cylinderBudget (sourceListSlotBudget C₀ B) *
        LineList.retainedSum (D:=D) (L:=pathLength B) (h:=h)
          (ℓ:=sourceLength B) (n:=listCutoff B) cut (LineList.geometryRetained hh K₀) +
      sourceWitnessError D hh K₀ cut := by
  let Q := cylinderBudget (sourceListSlotBudget C₀ B)
  calc
    _ ≤ ∑ w : NumericalLine D h (sourceLength B),
        (Q * (∑ l ∈ boundedLists (AttachedSpec w.line D (pathLength B)) (listCutoff B),
          assignedKernelIntegral w.line cut l (sourceRetained hh K₀ w)) +
        Q * residualWitnessIntegral (D:=D) (L:=pathLength B) w.line cut
          (sourceRetained hh K₀ w) (listCutoff B)) :=
      sum_le_sum (fun w hw => source_line_cylinder_reduction hh hB cut w)
    _ = Q * (∑ w : NumericalLine D h (sourceLength B),
        ∑ l ∈ boundedLists (AttachedSpec w.line D (pathLength B)) (listCutoff B),
          assignedKernelIntegral w.line cut l (sourceRetained hh K₀ w)) +
        sourceWitnessError D hh K₀ cut := by
      rw [sum_add_distrib,← mul_sum,← mul_sum]
      rfl
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left
        (retained_list_sum_le (D:=D) (h:=h) (ℓ:=sourceLength B) hh K₀ cut (listCutoff B))
        (cylinderBudget_nonneg _)) le_rfl

theorem source_retained_allowed_with_error (h : ℕ) (hh : 0 < h)
    (τ T C₀ K₀ : ℝ) (hτ : 1 ≤ τ) (hC₀ : 0 ≤ C₀) (hK₀ : 0 ≤ K₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      sourceAllowedRetainedSum D hh K₀ cut ≤
        B^(-(1+2*eta)*(sourceLength B:ℝ)) + sourceWitnessError D hh K₀ cut := by
  filter_upwards [LineList.source_retained_signed_sum h hh τ T C₀ K₀ 5 hτ hC₀ hK₀ (by norm_num),
    source_cylinder_budget C₀ hC₀,eventually_ge_atTop (1:ℝ)] with B hs hc hB
  intro D cut
  refine (source_allowed_retained_reduction D hh hB cut).trans ?_
  refine add_le_add ?_ le_rfl
  apply le_trans _ (hs D cut)
  apply mul_le_mul_of_nonneg_right hc
  exact sum_nonneg (fun x hx => LineList.assignedKernelIntegral_nonneg _ _ _ _)

end NumericalLine
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
