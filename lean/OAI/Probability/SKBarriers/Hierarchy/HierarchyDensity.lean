import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyGaussianLaw
import OAI.Probability.SKBarriers.SpinGlass.SpinStein
import OAI.Probability.SKBarriers.Hierarchy.HierarchyLevels

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPenalty_boundedDerivs (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) :
    BoundedDerivs (hierarchyPenalty n m u f) := by
  induction n generalizing u with
  | zero => exact hf.const_mul _
  | succ n ih =>
    let P : ParameterSpace (n+1) →L[ℝ] ParameterSpace n :=
      ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ
    exact (hf.const_mul _).add ((ih (fun i => m i.castSucc) (m (Fin.last n)) _
      (hf.gaussianStep _)).compCLM P)

section HierarchyDensity
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

def hierarchyPotential (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (s : S) (z : ParameterSpace n) : ℝ :=
  U s z-hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem hierarchyPotential_boundedDerivs (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (s : S) : BoundedDerivs (hierarchyPotential n m U s) := by
  have hu : BoundedDerivs (fun z => U s z) := by
    refine ⟨(U s).contDiff,‖U s‖,0,norm_nonneg _,le_rfl,?_,?_⟩
    · intro z; simp only [ContinuousLinearMap.fderiv]; exact le_rfl
    · intro z
      have he : fderiv ℝ (fun z => U s z) = fun _ => U s := by
        funext z; exact (U s).hasFDerivAt.fderiv
      rw [he]
      change ‖fderiv ℝ (Function.const (ParameterSpace n) (U s)) z‖ ≤ 0
      rw [fderiv_const]
      exact ContinuousLinearMap.opNorm_zero.le
  have hp := hierarchyPenalty_boundedDerivs n m 1 _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
  convert hu.add (hp.const_mul (-1)) using 1
  funext z
  simp only [hierarchyPotential,sub_eq_add_neg,neg_one_mul]

theorem hierarchyPotential_normalized (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) :
    (∫ sz : S × ParameterSpace n, Real.exp (hierarchyPotential n m U sz.1 sz.2)
      ∂(Measure.count : Measure S).prod (fiberGaussian n 0)) = 1 := by
  have hg (s : S) : HasExpGrowth (fun z => Real.exp (hierarchyPotential n m U s z)) := by
    simpa only [one_mul] using ((hierarchyPotential_boundedDerivs n m U s).exp_growths 1).1
  have hc (s : S) := Real.continuous_exp.comp (hierarchyPotential_boundedDerivs n m U s).1.continuous
  have hi (s : S) := (hg s).integrable_fiberGaussian n (hc s) 0
  change (∫ sz : S × ParameterSpace n, (Real.exp ∘ hierarchyPotential n m U sz.1) sz.2
    ∂(Measure.count : Measure S).prod (fiberGaussian n 0)) = 1
  rw [integral_prod _ (finite_fiberGaussian_integrable n _ hc hi),integral_count]
  change (∑ s, ∫ z, Real.exp (hierarchyPotential n m U s z) ∂fiberGaussian n 0) = 1
  rw [← integral_finsetSum _ (fun s _ => hi s)]
  have he (z : ParameterSpace n) : (∑ s, Real.exp (hierarchyPotential n m U s z)) =
      hierarchyPathWeight n m (affineLogPartition (fun _ => 0) U) z := by
    simp only [hierarchyPotential,← hierarchy_fixed_spin_density]
    rw [← Finset.mul_sum]
    change hierarchyPathWeight n m (affineLogPartition (fun _ => 0) U) z *
      (∑ s, hierarchyTerminalGibbs n U s z) = _
    rw [hierarchyTerminalGibbs_sum,mul_one]
  simp_rw [he]
  exact (hierarchyPathWeight_normalized n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0).2

theorem hierarchyGaussianLaw_eq_spinGaussian (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) :
    hierarchyGaussianLaw n m U = spinGaussianLaw n (hierarchyPotential n m U) 0 := by
  unfold hierarchyGaussianLaw spinGaussianLaw Measure.tilted
  rw [hierarchyPotential_normalized]
  simp only [div_one]
  congr 1
  funext sz
  congr 1
  exact hierarchy_fixed_spin_density n m _ (U sz.1) sz.2

omit [MeasurableSpace S] [MeasurableSingletonClass S] in

theorem hierarchyPotential_directional_cancellation (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (u z : ParameterSpace n)
    (hU : ∀ s, U s u = 0)
    (hi : ∀ k, k ≠ j → hierarchyAtom n m 1 k = 0 ∨
      TranslationInvariant (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) k) u) (s : S) :
    fderiv ℝ (hierarchyPotential n m U s) z u =
      -hierarchyAtom n m 1 j * fderiv ℝ (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) z u := by
  let f := affineLogPartition (fun _ => 0) U
  have hf := affineLogPartition_boundedDerivs (fun _ => 0) U
  have hp := hierarchyPenalty_boundedDerivs n m 1 f hf
  change fderiv ℝ (fun z => U s z-hierarchyPenalty n m 1 f z) z u = _
  rw [fderiv_fun_sub (U s).differentiableAt (hp.1.differentiable (by norm_num) z)]
  simp only [sub_apply,ContinuousLinearMap.fderiv,hU,zero_sub]
  rw [fderiv_hierarchyPenalty_apply n m 1 f hf]
  rw [Finset.sum_eq_single j]
  · ring
  · intro k _ hkj
    rcases hi k hkj with h | h
    · rw [h,zero_mul]
    · rw [h.fderiv_zero ((hierarchyLevel_boundedDerivs n m f hf k).1.differentiable (by norm_num)),mul_zero]
  · simp

end HierarchyDensity
end SK.Analytic

end
end
end
end
end
end
end

end OAI
