import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateRegularity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSpatialDerivativeBound
import Mathlib.Analysis.Calculus.LineDeriv.Basic

namespace OAI

/-! The coordinate derivatives are actual directional derivatives on
complex-horizontal and real-height space. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

def cubicThetaAxisVector : CubicThetaAxis → ℂ × ℝ
  | .x => (1,0)
  | .y => (Complex.I,0)
  | .height => (0,1)

def cubicThetaAxisFirst (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  deriv (fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
    (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)

def cubicThetaAxisSecond (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  deriv (deriv (fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t)))
    (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)

lemma cubicThetaCartesianPoint_self (p : ℂ × ℝ) :
    cubicThetaCartesianPoint p.1.re p.1.im p.2=p := by
  apply Prod.ext
  · exact Complex.re_add_im p.1
  · rfl

lemma cubicThetaAxisFirst_eq_fderiv (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ)
    {p : ℂ × ℝ} (hf : DifferentiableAt ℝ f p) :
    cubicThetaAxisFirst k f p=fderiv ℝ f p (cubicThetaAxisVector k) := by
  have hp := cubicThetaCartesianPoint_self p
  have hfc : DifferentiableAt ℝ f (cubicThetaCartesianPoint p.1.re p.1.im p.2) := hp.symm ▸ hf
  have h := cubicThetaFDeriv_coordinates p.1.re p.1.im p.2 hfc
  rw [hp] at h
  cases k
  · exact h.1.symm
  · exact h.2.1.symm
  · exact h.2.2.symm

lemma cubicThetaAxisFirst_line (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ)
    (x y v t : ℝ) :
    cubicThetaAxisFirst k f (cubicThetaCoordinateLine k x y v t)=
      deriv (fun w => f (cubicThetaCoordinateLine k x y v w)) t := by
  cases k <;> simp [cubicThetaAxisFirst,cubicThetaCoordinateLine,
    cubicThetaCoordinateCenter,cubicThetaCartesianPoint]

lemma cubicThetaAxisSecond_eq_fderiv (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ)
    {p : ℂ × ℝ} (hf : ContDiffAt ℝ 2 f p) :
    cubicThetaAxisSecond k f p=
      fderiv ℝ (fun q => fderiv ℝ f q (cubicThetaAxisVector k)) p (cubicThetaAxisVector k) := by
  have hfirst : cubicThetaAxisFirst k f=ᶠ[𝓝 p]
      (fun q => fderiv ℝ f q (cubicThetaAxisVector k)) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    exact cubicThetaAxisFirst_eq_fderiv k f (hq.differentiableAt (by norm_num))
  have hd : DifferentiableAt ℝ (fun q => fderiv ℝ f q (cubicThetaAxisVector k)) p :=
    (((hf.fderiv_right (m:=1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num))
  have hl : ContinuousAt (cubicThetaCoordinateLine k p.1.re p.1.im p.2)
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2) :=
    (cubicThetaCoordinateLine_continuous k _ _ _).continuousAt
  have hc := cubicThetaCoordinateLine_center k p.1.re p.1.im p.2
  rw [cubicThetaCartesianPoint_self] at hc
  have hlt : Tendsto (cubicThetaCoordinateLine k p.1.re p.1.im p.2)
      (𝓝 (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) (𝓝 p) := by
    simpa only [ContinuousAt,hc] using hl
  have he := hfirst.comp_tendsto hlt
  have haxis := cubicThetaAxisFirst_eq_fderiv k
    (fun q => fderiv ℝ f q (cubicThetaAxisVector k)) hd
  unfold cubicThetaAxisFirst at haxis
  rw [← haxis]
  unfold cubicThetaAxisSecond
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [he] with t ht
  change cubicThetaAxisFirst k f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t)=
    fderiv ℝ f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t) (cubicThetaAxisVector k) at ht
  rw [← ht,cubicThetaAxisFirst_line]

end CubicFirstMoment

end

end OAI
