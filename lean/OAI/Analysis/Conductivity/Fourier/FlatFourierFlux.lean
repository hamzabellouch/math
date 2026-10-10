import Mathlib
import OAI.Analysis.Conductivity.Geometry.FlatTorusPDE
import OAI.Analysis.Conductivity.Fourier.AngularPeriodization

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def flatModeFlux (s : Fin 3 → ℝ) (f : Coord3 → ℝ) (x : Coord3) : Coord3 :=
  ![fderiv ℝ f x (flatAxis 0),
    s 0*fderiv ℝ f x (flatAxis 1)+s 1*fderiv ℝ f x (flatAxis 2),
    s 1*fderiv ℝ f x (flatAxis 1)+s 2*fderiv ℝ f x (flatAxis 2)]

lemma flatModeFlux_smoothOn {s : Fin 3 → ℝ} {f : Coord3 → ℝ} {U : Set Coord3}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f U) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (flatModeFlux s f) U := by
  have hd := hf.fderiv_of_isOpen hU (m:=↑(⊤:ℕ∞)) (by simp)
  have he (i : Fin 3) := hd.clm_apply (contDiffOn_const (c:=flatAxis i))
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact he 0
  · exact (contDiffOn_const.mul (he 1)).add (contDiffOn_const.mul (he 2))
  · exact (contDiffOn_const.mul (he 1)).add (contDiffOn_const.mul (he 2))

lemma flatModeFlux_divergence {s : Fin 3 → ℝ} {f : Coord3 → ℝ} {x : Coord3}
    (hf : ContDiffAt ℝ (↑(⊤:ℕ∞)) f x) :
    coordinateDivergence (flatModeFlux s f) x=flatTensorLaplacian s f x := by
  have hd := (hf.fderiv_right (m:=1) (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))).differentiableAt (by simp)
  have he (i : Fin 3) :
      fderiv ℝ (fun y => fderiv ℝ f y (flatAxis i)) x=(fderiv ℝ (fderiv ℝ f) x).flip (flatAxis i) := by
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have he' (i : Fin 3) : DifferentiableAt ℝ (fun y => fderiv ℝ f y (flatAxis i)) x :=
    hd.clm_apply (differentiableAt_const _)
  have hsum := hf.isSymmSndFDerivAt (by simp)
  unfold coordinateDivergence
  rw [Fin.sum_univ_three]
  change fderiv ℝ (fun y => fderiv ℝ f y (flatAxis 0)) x (flatAxis 0)+
    fderiv ℝ (fun y => s 0*fderiv ℝ f y (flatAxis 1)+s 1*fderiv ℝ f y (flatAxis 2)) x (flatAxis 1)+
    fderiv ℝ (fun y => s 1*fderiv ℝ f y (flatAxis 1)+s 2*fderiv ℝ f y (flatAxis 2)) x (flatAxis 2)=_
  rw [fderiv_fun_add ((he' 1).const_mul _) ((he' 2).const_mul _),
    fderiv_fun_add ((he' 1).const_mul _) ((he' 2).const_mul _)]
  simp only [fderiv_const_mul (he' _),he,_root_.add_apply,
    _root_.smul_apply,ContinuousLinearMap.flip_apply,smul_eq_mul]
  unfold flatTensorLaplacian flatTensorLaplacianCLM
  simp only [_root_.add_apply,_root_.smul_apply,
    ContinuousMultilinearMap.apply_apply,smul_eq_mul,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [hsum.eq (flatAxis 2) (flatAxis 1)]
  ring

lemma flatModeFlux_periodic {s : Fin 3 → ℝ} {f : Coord3 → ℝ} {T : ℝ}
    (hf : AngularPeriodic T f) : AngularPeriodic T (flatModeFlux s f) := by
  intro n x
  unfold flatModeFlux
  rw [hf.fderiv n x]

lemma flatFourier_flux_divergence {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B) {x : Coord3} (hx : 0<x 0) :
    coordinateDivergence (flatModeFlux s (flatFourier s a phase)) x=0 := by
  rw [flatModeFlux_divergence ((flatFourier_smooth hs ha).contDiffAt
    ((axial_halfspace_open 0).mem_nhds hx)),flatFourier_harmonic hs ha hx]

end ScalarConductivity

end
end

end OAI
