import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.LaplacianLocality

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile170
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [ProperSpace X] in
lemma IsLaplacian.const_mul (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u A : X → ℝ} (hu : IsLaplacian m u A) (c : ℝ) :
    IsLaplacian m (fun x => c*u x) (fun x => c*A x) := by
  refine ⟨hu.1.const_mul c,hu.2.1.const_mul c,?_⟩
  intro w hw
  rw [integral_congr_ae (gamma_const_mul_left hfin hpar hu.1.2.1 hw.2.1 c),integral_const_mul,
    hu.2.2 w hw]
  simp_rw [mul_assoc c]
  rw [integral_const_mul]
  ring

lemma IsTestFunction.const_mul (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u : X → ℝ} (hu : IsTestFunction m u) (c : ℝ) : IsTestFunction m (fun x => c*u x) := by
  have hg := (laplacian_isLaplacian hu.1).const_mul hfin hpar c
  obtain ⟨B,hB⟩ := hu.2.1
  refine ⟨⟨_,hg⟩,⟨|c| * B,fun x => ?_⟩,hu.2.2.1.const_mul c,?_⟩
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)
  · exact (sobolev_congr_ae (hg.ae_laplacian hfin)).mpr (hu.2.2.2.const_mul c)

omit [ProperSpace X] in
lemma isLaplacian_zero (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m) :
    IsLaplacian m (0 : X → ℝ) 0 := by
  have hs : Sobolev m (0 : X → ℝ) :=
    sobolev_of_lipschitz_compactSupport hfin (LipschitzWith.const 0) HasCompactSupport.zero
  refine ⟨hs,MemLp.zero,?_⟩
  intro w hw
  have hz : gamma m (0 : X → ℝ) w =ᵐ[m] 0 := by
    filter_upwards [gamma_zero_on_const_set hfin hpar hs.2.1 hw.2.1 MeasurableSet.univ
      (c := 0) (ae_of_all _ fun x hx => rfl)] with x hx
    exact hx (mem_univ x)
  rw [integral_congr_ae hz]
  simp only [Pi.zero_apply,zero_mul,integral_zero,neg_zero]

lemma isTestFunction_zero (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m) :
    IsTestFunction m (0 : X → ℝ) := by
  have hg := isLaplacian_zero hfin hpar
  refine ⟨⟨0,hg⟩,⟨0,fun x => by simp⟩,⟨0,LipschitzWith.const 0⟩,?_⟩
  exact (sobolev_congr_ae (hg.ae_laplacian hfin)).mpr hg.1
end WeakHessian

end
end InlinedFile170

end OAI
