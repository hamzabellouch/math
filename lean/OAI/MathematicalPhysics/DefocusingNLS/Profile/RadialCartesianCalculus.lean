import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianSmooth
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffLaplacian
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! Cartesian differentiation of a radial function through its squared radius. -/

open scoped ContDiff Laplacian
open Set Filter Topology
namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radial_second_directional_eq (f : E → ℂ) (x v : E)
    (hf : ContDiffAt ℝ 2 f x) :
    iteratedFDeriv ℝ 2 f x ![v,v] =
      fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem radialSquareLift_fderiv (q : ℝ → ℂ) (x v : E)
    (hq : DifferentiableAt ℝ q (‖x‖^2)) :
    fderiv ℝ (fun y : E => q (‖y‖^2)) x v =
      ((2 * inner ℝ x v : ℝ) : ℂ) * deriv q (‖x‖^2) := by
  have h := hq.hasFDerivAt.comp x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  simp only [Function.comp_def] at h
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply,fderiv_eq_smul_deriv]
  ring

theorem radialSquareLift_second (q : ℝ → ℂ) (x v : E)
    (hq : ContDiffAt ℝ 2 q (‖x‖^2)) :
    iteratedFDeriv ℝ 2 (fun y : E => q (‖y‖^2)) x ![v,v] =
      ((2 * inner ℝ x v : ℝ) : ℂ)^2 * deriv (deriv q) (‖x‖^2) +
        ((2 * ‖v‖^2 : ℝ) : ℂ) * deriv q (‖x‖^2) := by
  have hq' : DifferentiableAt ℝ (deriv q) (‖x‖^2) :=
    (hq.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he : (fun y : E => fderiv ℝ (fun z : E => q (‖z‖^2)) y v) =ᶠ[nhds x]
      (fun y => ((2 * inner ℝ y v : ℝ) : ℂ) * deriv q (‖y‖^2)) := by
    have hn : ContinuousAt (fun y : E => ‖y‖^2) x := (contDiff_norm_sq ℝ (n := 2)).continuous.continuousAt
    filter_upwards [hn (hq.eventually (by norm_num))] with y hy
    change ContDiffAt ℝ 2 q (‖y‖^2) at hy
    exact radialSquareLift_fderiv q y v (hy.differentiableAt (by norm_num))
  have hi := ((hasFDerivAt_id x).inner ℝ (hasFDerivAt_const v x)).const_mul 2
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hi
  have hd := hq'.hasFDerivAt.comp x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hf : ContDiffAt ℝ 2 (fun y : E => q (‖y‖^2)) x := by
    simpa only [Function.comp_def] using hq.comp x (contDiff_norm_sq ℝ).contDiffAt
  have hm := hc.mul hd
  simp only [Function.comp_def,id_eq,Complex.ofRealCLM_apply] at hm
  change HasFDerivAt (fun y : E => ((2*inner ℝ y v : ℝ) : ℂ)*deriv q (‖y‖^2)) _ x at hm
  rw [radial_second_directional_eq _ x v hf,he.fderiv_eq,hm.fderiv]
  simp [fderivInnerCLM_apply, fderiv_eq_smul_deriv, Complex.real_smul,
    inner_self_eq_norm_sq_to_K]
  ring

theorem radialSquareLift_laplacian (q : ℝ → ℂ) (x : E)
    (hq : ContDiffAt ℝ 2 q (‖x‖^2)) :
    Δ (fun y : E => q (‖y‖^2)) x =
      ((4 * ‖x‖^2 : ℝ) : ℂ) * deriv (deriv q) (‖x‖^2) +
        24 * deriv q (‖x‖^2) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 12) ℝ)]
  simp_rw [radialSquareLift_second q x _ hq]
  have hb (j : Fin 12) : ‖EuclideanSpace.basisFun (Fin 12) ℝ j‖ = 1 :=
    (EuclideanSpace.basisFun (Fin 12) ℝ).orthonormal.norm_eq_one j
  simp_rw [hb]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have hs : (∑ j : Fin 12, ((2 * inner ℝ x (EuclideanSpace.basisFun (Fin 12) ℝ j) : ℝ) : ℂ)^2) =
      ((4 * ‖x‖^2 : ℝ) : ℂ) := by
    simp_rw [Complex.ofReal_mul, mul_pow]
    rw [← Finset.mul_sum]
    simp_rw [← Complex.ofReal_pow]
    rw [← Complex.ofReal_sum,
      (EuclideanSpace.basisFun (Fin 12) ℝ).sum_sq_inner_left]
    norm_num
  rw [hs]
  simp
  ring

end DefocusingNLS

end OAI
