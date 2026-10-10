import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ScaledWindow
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.KernelL1Concentration

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryGaussianWindow
open MeasureTheory OrdinarySharpWindow

noncomputable def bumpMass : ℝ := ∫x : ℝ,bump x
noncomputable def bumpMoment : ℝ := ∫x : ℝ,bump x*|x|
noncomputable def dilateKernel (w x : ℝ) : ℝ := bump (x/w)

lemma bump_nonneg (x : ℝ) : 0≤bump x := (Real.exp_pos _).le

lemma bump_integrable : Integrable bump := by
  exact integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<2)

lemma bumpMoment_integrable : Integrable (fun x : ℝ=>bump x*|x|) := by
  have hh := (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ)<2)).norm
  convert hh using 1
  ext x
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  exact mul_comm _ _

lemma bumpMass_pos : 0<bumpMass := by
  unfold bumpMass bump
  rw [integral_gaussian]
  exact Real.sqrt_pos.2 (by positivity)

lemma bumpMoment_nonneg : 0≤bumpMoment :=
  integral_nonneg (fun point=>mul_nonneg (bump_nonneg point) (abs_nonneg point))

lemma dilateKernel_integrable {w : ℝ} (hw : 0<w) : Integrable (dilateKernel w) := by
  have hh := (integrable_comp_mul_right_iff bump (inv_ne_zero hw.ne')).mpr bump_integrable
  change Integrable (fun x : ℝ=>bump (x/w))
  simpa only [div_eq_mul_inv] using hh

lemma dilateKernel_mass {w : ℝ} (hw : 0<w) :
    (∫x : ℝ,dilateKernel w x)=w*bumpMass := by
  unfold dilateKernel bumpMass
  rw [Measure.integral_comp_div]
  simp only [abs_of_pos hw,smul_eq_mul]

lemma dilateKernel_moment_eq {w : ℝ} (hw : 0<w) (x : ℝ) :
    dilateKernel w x*|x|=w*(bump (x/w)*|x/w|) := by
  unfold dilateKernel
  rw [abs_div,abs_of_pos hw]
  field_simp

lemma dilateKernel_moment_integrable {w : ℝ} (hw : 0<w) :
    Integrable (fun x : ℝ=>dilateKernel w x*|x|) := by
  simp_rw [dilateKernel_moment_eq hw]
  have hh := (integrable_comp_mul_right_iff (fun x : ℝ=>bump x*|x|)
    (inv_ne_zero hw.ne')).mpr bumpMoment_integrable
  have hh' := hh.const_mul w
  simpa only [←div_eq_mul_inv] using hh'

lemma dilateKernel_moment {w : ℝ} (hw : 0<w) :
    (∫x : ℝ,dilateKernel w x*|x|)=w^2*bumpMoment := by
  simp_rw [dilateKernel_moment_eq hw]
  rw [MeasureTheory.integral_const_mul]
  have he := Measure.integral_comp_div (fun x : ℝ=>bump x*|x|) w
  change (∫x : ℝ,bump (x/w)*|x/w|)=_ at he
  rw [he]
  simp only [abs_of_pos hw,smul_eq_mul]
  unfold bumpMoment
  ring

lemma scaledWindow_square_integrable {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {w : ℝ} (hw : 0<w) : Integrable (fun x : ℝ=>‖scaledWindow s a u w x‖^2) := by
  simp_rw [scaledWindow_eq]
  have hh := (integrable_comp_mul_right_iff
    (fun x : ℝ=>‖window s a (fun n=>u n/w) x‖^2) (inv_ne_zero hw.ne')).mpr
    (window_square_integrable s a _)
  simpa only [←div_eq_mul_inv] using hh

lemma kernelWindow_dilate {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ) (w : ℝ) :
    kernelWindow s a u (dilateKernel w)=scaledWindow s a u w := rfl

lemma scaledWindow_l1_concentration {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {c q w : ℝ} (hcentres : ∀n∈s,c≤u n ∧ u n≤c+1) (hq : 0<q) (hw : 0<w) :
    (∫x : ℝ,‖scaledWindow s a u w x‖)≤
      3*q+(∫x : ℝ,‖scaledWindow s a u w x‖^2)/(4*q)+
        (∑n∈s,‖a n‖)*(w^2*bumpMoment) := by
  have hh := kernel_l1_concentration s a u (dilateKernel_integrable hw)
    (fun x=>bump_nonneg _) (dilateKernel_moment_integrable hw)
    (scaledWindow_square_integrable s a u hw) hcentres hq
  simpa only [kernelWindow_dilate,dilateKernel_moment hw] using hh

end OrdinaryGaussianWindow

end

end OAI
