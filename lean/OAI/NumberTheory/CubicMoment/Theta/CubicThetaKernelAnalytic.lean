import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAllGridEquation
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace OAI

/-! Real analyticity of the coordinate slices of the kernel. This
supplies both differentiability levels needed by the spectral operator. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaHeightPower_analytic (s : ℂ) {v : ℝ} (hv : 0<v) :
    AnalyticAt ℝ (fun t : ℝ => (t:ℂ)^s) v := by
  have h : AnalyticAt ℂ (fun z : ℂ => z^s) (v:ℂ) :=
    analyticAt_id.cpow analyticAt_const (Complex.ofReal_mem_slitPlane.mpr hv)
  exact h.restrictScalars.comp (Complex.ofRealCLM.analyticAt v)

lemma cubicThetaQuadratic_analytic (s : ℂ) (b x : ℝ) (hx : 0<x^2+b) :
    AnalyticAt ℝ (cubicThetaQuadraticPower s b) x := by
  have hq : AnalyticAt ℝ (fun t : ℝ => t^2+b) x := by fun_prop
  exact (cubicThetaHeightPower_analytic s hx).comp (f:=fun t : ℝ => t^2+b) (x:=x) hq

lemma cubicThetaCartesian_x_analytic (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    AnalyticAt ℝ (fun t : ℝ => cubicThetaCartesianKernel s t y v) x := by
  have he : (fun t : ℝ => cubicThetaCartesianKernel s t y v)=
      (fun t : ℝ => (v:ℂ)^s*cubicThetaQuadraticPower (-s) (y^2+v^2) t) := by
    funext t
    unfold cubicThetaCartesianKernel cubicThetaQuadraticPower
    rw [add_assoc]
  rw [he]
  exact analyticAt_const.mul (cubicThetaQuadratic_analytic (-s) (y^2+v^2) x
    (by nlinarith [sq_nonneg x,sq_nonneg y,sq_pos_of_pos hv]))

lemma cubicThetaCartesian_y_analytic (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    AnalyticAt ℝ (fun t : ℝ => cubicThetaCartesianKernel s x t v) y := by
  have he : (fun t : ℝ => cubicThetaCartesianKernel s x t v)=
      (fun t : ℝ => cubicThetaCartesianKernel s t x v) := by
    funext t
    unfold cubicThetaCartesianKernel
    rw [add_comm (x^2) (t^2)]
  rw [he]
  exact cubicThetaCartesian_x_analytic s y x hv

lemma cubicThetaCartesian_v_analytic (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    AnalyticAt ℝ (fun t : ℝ => cubicThetaCartesianKernel s x y t) v := by
  rw [cubicThetaCartesian_vertical]
  exact (cubicThetaHeightPower_analytic s hv).mul
    (cubicThetaQuadratic_analytic (-s) (x^2+y^2) v
      (by nlinarith [sq_nonneg x,sq_nonneg y,sq_pos_of_pos hv]))

end CubicFirstMoment

end

end OAI
