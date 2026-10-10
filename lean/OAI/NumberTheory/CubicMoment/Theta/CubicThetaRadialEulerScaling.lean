import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialProfileEquation

namespace OAI

/-! The radial Euler operator commutes with positive changes of height. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaRadialEuler_scale {f : ℝ → ℂ} {r v : ℝ} (hr : 0<r)
    (hf : ContDiffAt ℝ 2 f (v/r)) :
    cubicThetaRadialEuler (fun t => f (t/r)) v=cubicThetaRadialEuler f (v/r) := by
  have hg : ContDiffAt ℝ 2 (fun t : ℝ => t/r) v :=
    (contDiff_id.div_const r).contDiffAt
  have hd := (hf.differentiableAt (by norm_num)).hasDerivAt.scomp v
    ((hasDerivAt_id v).div_const r)
  have hdd := cubicThetaSecondChain (h:=fun t : ℝ => t/r) (x:=v) hf hg
  have hdlin : deriv (fun t : ℝ => t/r)=(fun _ => 1/r) := by
    funext t
    simp only [deriv_div_const,deriv_id'']
  simp only [Function.comp_def,hdlin,deriv_const,zero_smul,add_zero,
    Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one] at hdd
  have hd' : deriv (fun t => f (t/r)) v=(1/r:ℝ) • deriv f (v/r) := hd.deriv
  unfold cubicThetaRadialEuler
  rw [hd',hdd]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one]
  have hr0 : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  field_simp

lemma cubicThetaRadialEuler_const_mul (c : ℂ) (f : ℝ → ℂ) (v : ℝ) :
    cubicThetaRadialEuler (fun t => c*f t) v=c*cubicThetaRadialEuler f v := by
  simp only [cubicThetaRadialEuler,deriv_const_mul_field']
  ring

lemma cubicThetaRadialEuler_sub {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (v : ℝ) :
    cubicThetaRadialEuler (fun t => f t-g t) v=
      cubicThetaRadialEuler f v-cubicThetaRadialEuler g v := by
  have hd : deriv (fun t => f t-g t)=(fun t => deriv f t-deriv g t) := by
    funext t
    exact deriv_sub (hf.differentiable (by simp) t) (hg.differentiable (by simp) t)
  have hf' : Differentiable ℝ (deriv f) :=
    ((contDiff_infty_iff_deriv.mp hf).2).differentiable (by simp)
  have hg' : Differentiable ℝ (deriv g) :=
    ((contDiff_infty_iff_deriv.mp hg).2).differentiable (by simp)
  unfold cubicThetaRadialEuler
  have hdd : deriv (fun t => deriv f t-deriv g t) v=
      deriv (deriv f) v-deriv (deriv g) v := deriv_sub (hf' v) (hg' v)
  rw [hd,hdd]
  ring

end CubicFirstMoment

end

end OAI
