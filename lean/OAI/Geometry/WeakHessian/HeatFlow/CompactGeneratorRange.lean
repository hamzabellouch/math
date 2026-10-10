import Mathlib
import OAI.Geometry.WeakHessian.Calculus.CompactCoreAnnihilator
import OAI.Geometry.WeakHessian.LocalBounds.TestScaling

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile171
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

def compactGeneratorRange (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m) :
    Submodule ℝ (Lp ℝ 2 m) where
  carrier := {f | ∃ g : X → ℝ,IsTestFunction m g ∧ HasCompactSupport g ∧
    ∃ u A : Lp ℝ 2 m,g =ᵐ[m] u ∧ IsLaplacian m g A ∧ f = u-A}
  zero_mem' := by
    refine ⟨0,isTestFunction_zero hfin hpar,HasCompactSupport.zero,0,0,
      (Lp.coeFn_zero ℝ 2 m).symm,?_,by simp⟩
    exact (isLaplacian_zero hfin hpar).congr_ae EventuallyEq.rfl (Lp.coeFn_zero ℝ 2 m).symm
  add_mem' := by
    rintro f j ⟨g,hg,hgc,u,A,hge,hgA,rfl⟩ ⟨k,hk,hkc,v,B,hke,hkB,rfl⟩
    refine ⟨fun x => g x+k x,hg.add hfin hpar hk,hgc.add hkc,u+v,A+B,?_,?_,by abel⟩
    · filter_upwards [hge,hke,Lp.coeFn_add u v] with x hx hy hz
      simpa only [Pi.add_apply,hx,hy] using hz.symm
    · exact (hgA.add hfin hpar hkB).congr_ae EventuallyEq.rfl (Lp.coeFn_add A B).symm
  smul_mem' := by
    rintro c f ⟨g,hg,hgc,u,A,hge,hgA,rfl⟩
    refine ⟨fun x => c*g x,hg.const_mul hfin hpar c,hgc.mul_left,c • u,c • A,?_,?_,smul_sub c u A⟩
    · filter_upwards [hge,Lp.coeFn_smul c u] with x hx hy
      simpa only [Pi.smul_apply,smul_eq_mul,hx] using hy.symm
    · exact (hgA.const_mul hfin hpar c).congr_ae EventuallyEq.rfl (Lp.coeFn_smul c A).symm

variable [SigmaFinite m]
lemma RCD.compactGeneratorRange_dense {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X) :
    (compactGeneratorRange hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2)).topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply hrcd.compact_core_annihilator_zero hN hfull hfin o f
  intro g hg hgc u A hgu hgA
  have hm : u-A ∈ compactGeneratorRange hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2) :=
    ⟨g,hg,hgc,u,A,hgu,(laplacian_isLaplacian hg.1).congr_ae EventuallyEq.rfl hgA,rfl⟩
  exact Submodule.inner_left_of_mem_orthogonal hm hf

end WeakHessian

end
end InlinedFile171

end OAI
