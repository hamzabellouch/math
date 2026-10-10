import OAI.NumberTheory.CubicMoment.Estimates.GaussianTrace
import Mathlib.Analysis.Distribution.TemperateGrowth

namespace OAI

/-! Polynomially controlled factors of all derivatives of the radial Gaussian. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

private lemma temperate_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P : ℂ → F} (hP : P.HasTemperateGrowth) :
    (fderiv ℝ P).HasTemperateGrowth := by
  refine ⟨hP.1.fderiv_right (by simp),?_⟩
  intro n
  obtain ⟨k,C,hC⟩ := hP.2 (n+1)
  exact ⟨k,C,fun z => by simpa only [norm_iteratedFDeriv_fderiv] using hC z⟩

private lemma temperate_smulRight {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : ℂ → (ℂ →L[ℝ] ℝ)} {P : ℂ → F}
    (hL : L.HasTemperateGrowth) (hP : P.HasTemperateGrowth) :
    (fun z => (L z).smulRight (P z)).HasTemperateGrowth :=
  (ContinuousLinearMap.smulRightL ℝ ℂ F).bilinear_hasTemperateGrowth hL hP

def radialGaussian (a : ℝ) (z : ℂ) : ℝ := Real.exp (-a*‖z‖^2)

def gaussianLogDerivative (a : ℝ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (-2*a) • innerSL ℝ

lemma radialGaussian_smooth (a : ℝ) : ContDiff ℝ ∞ (radialGaussian a) := by
  exact (contDiff_const.mul (contDiff_norm_sq ℝ)).exp

lemma radialGaussian_fderiv (a : ℝ) (z : ℂ) :
    fderiv ℝ (radialGaussian a) z = radialGaussian a z • gaussianLogDerivative a z := by
  unfold radialGaussian
  have hd : DifferentiableAt ℝ (fun w : ℂ => ‖w‖^2) z :=
    (differentiable_id.norm_sq ℝ).differentiableAt
  rw [fderiv_exp (hd.const_mul (-a)),fderiv_const_mul hd,fderiv_norm_sq_apply]
  ext w
  simp only [gaussianLogDerivative,smul_apply,smul_smul,smul_eq_mul]
  ring

lemma radialGaussian_derivative_factor (a : ℝ) (n : ℕ) :
    ∃ P : ℂ → ℂ [×n]→L[ℝ] ℝ, P.HasTemperateGrowth ∧
      ∀ z, iteratedFDeriv ℝ n (radialGaussian a) z = radialGaussian a z • P z := by
  induction n with
  | zero =>
    let P : ℂ → ℂ [×0]→L[ℝ] ℝ := fun _ => (continuousMultilinearCurryFin0 ℝ ℂ ℝ).symm 1
    refine ⟨P,Function.HasTemperateGrowth.const _,?_⟩
    intro z
    rw [iteratedFDeriv_zero_eq_comp]
    change (continuousMultilinearCurryFin0 ℝ ℂ ℝ).symm (radialGaussian a z) = _
    rw [← map_smul]
    simp only [smul_eq_mul,mul_one]
  | succ n ih =>
    obtain ⟨P,hP,hfactor⟩ := ih
    let Q : ℂ → ℂ →L[ℝ] (ℂ [×n]→L[ℝ] ℝ) := fun z =>
      (gaussianLogDerivative a z).smulRight (P z) + fderiv ℝ P z
    have hQ : Q.HasTemperateGrowth :=
      (temperate_smulRight (gaussianLogDerivative a).hasTemperateGrowth hP).add (temperate_fderiv hP)
    let e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => ℂ) ℝ).symm
    refine ⟨fun z => e (Q z),by
      convert e.toContinuousLinearEquiv.hasTemperateGrowth.comp hQ using 1
      rfl,?_⟩
    intro z
    have he : iteratedFDeriv ℝ n (radialGaussian a) = fun z => radialGaussian a z • P z := funext hfactor
    rw [iteratedFDeriv_succ_eq_comp_left,he]
    change e (fderiv ℝ (fun z => radialGaussian a z • P z) z) = _
    have hd : fderiv ℝ (fun z => radialGaussian a z • P z) z = radialGaussian a z • Q z := by
      rw [fderiv_fun_smul (radialGaussian_smooth a |>.differentiable (by simp) |>.differentiableAt)
        (hP.1.differentiable (by simp) |>.differentiableAt),radialGaussian_fderiv]
      ext w
      simp only [Q,add_apply,smul_apply,
        ContinuousLinearMap.smulRight_apply,smul_add,smul_smul]
      module
    rw [hd,map_smul]

end CubicFirstMoment

end

end OAI
