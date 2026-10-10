import Mathlib
import OAI.Analysis.Conductivity.Geometry.FlatTorusPDE
import OAI.Analysis.Conductivity.Fourier.PeriodicFamilyCorrection

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma flatTensorLaplacian_add {s : Fin 3→ℝ} {f g : Coord3→ℝ} {x : Coord3}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    flatTensorLaplacian s (fun y => f y+g y) x=
      flatTensorLaplacian s f x+flatTensorLaplacian s g x := by
  unfold flatTensorLaplacian
  rw [fun_iteratedFDeriv_add_apply hf hg,map_add]

lemma axial_affine_fderiv (α β : ℝ) (x : Coord3) :
    fderiv ℝ (fun y : Coord3 => α*y 0+β) x=α • ContinuousLinearMap.proj 0 := by
  have hh := (((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 3 => ℝ) 0).hasFDerivAt (x:=x)).const_mul α).add_const β
  exact hh.fderiv

lemma flatTensorLaplacian_axial_affine (s : Fin 3→ℝ) (α β : ℝ) (x : Coord3) :
    flatTensorLaplacian s (fun y => α*y 0+β) x=0 := by
  have he : fderiv ℝ (fun y : Coord3 => α*y 0+β)=fun _ => α • ContinuousLinearMap.proj 0 :=
    funext (axial_affine_fderiv α β)
  unfold flatTensorLaplacian flatTensorLaplacianCLM
  simp only [_root_.add_apply,_root_.smul_apply,
    ContinuousMultilinearMap.apply_apply,smul_eq_mul,iteratedFDeriv_two_apply,he,
    fderiv_fun_const,Pi.zero_apply,_root_.zero_apply,mul_zero,add_zero]

def affineFourierField (s : Fin 3→ℝ) (a phase : (Fin 2→ℤ)→ℝ) (α β : ℝ) (x : Coord3) : ℝ :=
  α*x 0+β+flatFourier s a phase x

lemma affineFourierField_smooth {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B) (α β : ℝ) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (affineFourierField s a phase α β) {x | 0<x 0} :=
  (show ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : Coord3 => α*x 0+β) by fun_prop).contDiffOn.add
    (flatFourier_smooth hs ha)

lemma affineFourierField_periodic (s : Fin 3→ℝ) (a phase : (Fin 2→ℤ)→ℝ) (α β : ℝ) :
    AngularPeriodic (2*Real.pi) (affineFourierField s a phase α β) := by
  intro n x
  unfold affineFourierField
  rw [flatFourier_angularPeriodic s a phase n x]
  change α*(x 0+0)+β+_=α*x 0+β+_
  rw [add_zero]

lemma affineFourierField_harmonic {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B) (α β : ℝ)
    {x : Coord3} (hx : 0<x 0) : flatTensorLaplacian s (affineFourierField s a phase α β) x=0 := by
  have hf := (flatFourier_smooth (phase:=phase) hs ha).contDiffAt ((axial_halfspace_open 0).mem_nhds hx)
  unfold affineFourierField
  rw [flatTensorLaplacian_add (by fun_prop)
    (hf.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))),
    flatTensorLaplacian_axial_affine,flatFourier_harmonic hs ha hx,add_zero]

lemma affineFourierField_fderiv {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B) (α β : ℝ)
    {x : Coord3} (hx : 0<x 0) :
    fderiv ℝ (affineFourierField s a phase α β) x=
      α • ContinuousLinearMap.proj 0+fderiv ℝ (flatFourier s a phase) x := by
  unfold affineFourierField
  rw [fderiv_fun_add (by fun_prop) (((flatFourier_smooth hs ha).contDiffAt
    ((axial_halfspace_open 0).mem_nhds hx)).differentiableAt (by simp)),axial_affine_fderiv]

end ScalarConductivity

end
end

end OAI
