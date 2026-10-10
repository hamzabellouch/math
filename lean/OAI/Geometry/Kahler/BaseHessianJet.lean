import OAI.Geometry.Kahler.BaseJetNorms

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

abbrev ComplexJet2 := ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Base) ℂ
abbrev RealJet2 := ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Base) ℝ

def complexHessianJet (i j : Fin 2) : ComplexJet2 →L[ℝ] ℂ :=
  (1/4 : ℂ) •
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Base) ℂ
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] +
    Complex.I • ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Base) ℂ
      ![EuclideanSpace.single i 1, Complex.I • EuclideanSpace.single j 1] -
    Complex.I • ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Base) ℂ
      ![Complex.I • EuclideanSpace.single i 1, EuclideanSpace.single j 1] +
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Base) ℂ
      ![Complex.I • EuclideanSpace.single i 1, Complex.I • EuclideanSpace.single j 1])

lemma dz_dbar_jet {f : Base → ℂ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) (i j : Fin 2) :
    dzBase (fun x => dbarBase f x j) z i = complexHessianJet i j (iteratedFDeriv ℝ 2 f z) := by
  have hd := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he := ((wirtingerCLM true j).hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  rw [dbarBase_asCLM] at ⊢
  simp only [dzBase,he,ContinuousLinearMap.comp_apply,wirtingerCLM_apply]
  simp only [complexHessianJet,smul_apply,add_apply,
    sub_apply,ContinuousMultilinearMap.apply_apply,smul_eq_mul,
    iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,ite_true]
  have hi : Complex.I*Complex.I = -1 := Complex.I_mul_I
  linear_combination -(fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single i 1)
    (Complex.I • EuclideanSpace.single j 1))/4*hi

def realHessianJet (i j : Fin 2) : RealJet2 →L[ℝ] ℂ :=
  (complexHessianJet i j).comp
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin 2 => Base) ℝ ℂ Complex.ofRealCLM)

lemma baseHessian_eq_jet {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) (i j : Fin 2) :
    baseHessian f z i j = realHessianJet i j (iteratedFDeriv ℝ 2 f z) := by
  have hfc : ContDiffAt ℝ ∞ (fun x => (f x:ℂ)) z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  rw [baseHessian,dz_dbar_jet hfc]
  change complexHessianJet i j (iteratedFDeriv ℝ 2 (Complex.ofRealCLM ∘ f) z) = _
  rw [Complex.ofRealCLM.iteratedFDeriv_comp_left hf (WithTop.coe_le_coe.mpr le_top)]
  rfl

def realHessianValueJet (v : Base) : RealJet2 →L[ℝ] ℝ :=
  Complex.reCLM.comp (∑ i : Fin 2, ∑ j : Fin 2, (v i*star (v j)) • realHessianJet i j)

lemma baseHessian_value_eq_jet {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) (v : Base) :
    (∑ i, ∑ j, baseHessian f z i j*v i*star (v j)).re =
      realHessianValueJet v (iteratedFDeriv ℝ 2 f z) := by
  simp only [realHessianValueJet,ContinuousLinearMap.comp_apply,sum_apply,
    smul_apply,smul_eq_mul,Complex.reCLM_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [baseHessian_eq_jet hf]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
