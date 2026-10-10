import OAI.Analysis.LipschitzHilbert.Fourier.VerticalConvolutionL2
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! The vertical fundamental theorem of calculus in the quadratic form
used to compare the two orders of convolution and sampling. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def verticalSchwartzDeriv (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  (SchwartzMap.evalCLM ℝ (ℝ×ℝ) ℂ (0,1)) (SchwartzMap.fderivCLM ℝ (ℝ×ℝ) ℂ f)

theorem verticalSchwartzDeriv_apply (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    verticalSchwartzDeriv f z=fderiv ℝ f z (0,1) := rfl

theorem verticalPath_hasDerivAt (f : SchwartzMap (ℝ×ℝ) ℂ) (x y delta theta : ℝ) :
    HasDerivAt (fun a : ℝ => f (x,y+a*delta))
      (delta • verticalSchwartzDeriv f (x,y+theta*delta)) theta := by
  have hp : HasDerivAt (fun a : ℝ => (x,y+a*delta)) (0,delta) theta := by
    simpa using (hasDerivAt_const theta x).prodMk
      ((hasDerivAt_const theta y).add ((hasDerivAt_id theta).mul_const delta))
  have h := (f.hasFDerivAt (x,y+theta*delta)).comp_hasDerivAt theta hp
  have heq : (fderiv ℝ f (x,y+theta*delta)) (0,delta)=
      delta • verticalSchwartzDeriv f (x,y+theta*delta) := by
    rw [verticalSchwartzDeriv_apply]
    have hvec : ((0,delta) : ℝ×ℝ)=delta • ((0,1) : ℝ×ℝ) := by ext <;> simp
    rw [hvec,map_smul]
  simpa only [Function.comp_def,heq] using h

theorem vertical_secant_energy (f : SchwartzMap (ℝ×ℝ) ℂ) (x y0 y1 : ℝ) :
    ‖f (x,y1)-f (x,y0)‖^2≤(y1-y0)^2*
      ∫ theta in (0:ℝ)..1, ‖verticalSchwartzDeriv f (x,y0+theta*(y1-y0))‖^2 := by
  let d := y1-y0
  let H := fun theta : ℝ => verticalSchwartzDeriv f (x,y0+theta*d)
  have hH : Continuous H := (verticalSchwartzDeriv f).continuous.comp (by fun_prop)
  have hi : IntervalIntegrable (fun theta => d • H theta) volume 0 1 :=
    ((continuous_const : Continuous (fun _ : ℝ => d)).smul hH).intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun theta _ => verticalPath_hasDerivAt f x y0 d theta) hi
  have heq : f (x,y1)-f (x,y0)=d • ∫ theta in (0:ℝ)..1, H theta := by
    simpa only [zero_mul,add_zero,one_mul,show y0+d=y1 by dsimp [d]; ring,
      intervalIntegral.integral_smul] using hftc.symm
  have hH2 : Integrable (fun theta => ‖H theta‖^2) (volume.restrict (Ioc (0:ℝ) 1)) :=
    (hH.norm.pow 2).intervalIntegrable 0 1 |>.1
  have hc := (weighted_integral_cauchySchwarz (volume.restrict (Ioc (0:ℝ) 1))
    (fun _ => 1) (fun theta => ‖H theta‖) measurable_const hH.measurable.norm
    (fun _ => zero_le_one) (fun _ => norm_nonneg _) (integrable_const 1)
    (by simpa only [one_mul] using hH2)).2
  simp only [one_mul,integral_const,smul_eq_mul,mul_one] at hc
  have hm : (volume.restrict (Ioc (0:ℝ) 1)).real univ=1 := by
    rw [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc]
    norm_num
  rw [hm,one_mul] at hc
  have hn : ‖∫ theta in (0:ℝ)..1, H theta‖≤∫ theta in Ioc (0:ℝ) 1, ‖H theta‖ := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact norm_integral_le_integral_norm _
  rw [heq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  simp only [intervalIntegral.integral_of_le zero_le_one] at hn ⊢
  apply mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc) (sq_nonneg d)

end LipschitzHilbert.PacketRepresentation

end

end OAI
