import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScatteringMeromorphic

namespace OAI

/-! In Re(s)>1 the explicit scattering coefficient has no possible pole
except s=4/3. The denominator is controlled by its convergent Euler product. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_principalZeta_right_ne_zero {s : ℂ} (hs : 1<s.re) :
    principalIdealZeta s≠0 := by
  rw [principalIdealZeta_right hs]
  exact idealDirichlet_ne_zero (fun _ => (1:ℂ)) (by simp) rfl (by simp) hs

lemma cubicThetaScattering_local_denominator {s : ℂ} (hs : 1<s.re) :
    1-(3:ℂ)^(2-3*s)≠0 := by
  have hn : ‖(3:ℂ)^(2-3*s)‖<1 := by
    rw [show (3:ℂ)=((3:ℝ):ℂ) by norm_num]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      zero_mul,sub_zero,Complex.ofReal_ofNat]
    linarith
  intro hz
  have he : (3:ℂ)^(2-3*s)=1 := (sub_eq_zero.mp hz).symm
  rw [he,norm_one] at hn
  exact (lt_irrefl 1) hn

theorem cubicThetaConstantContinuation_regular {s : ℂ} (hs : 1<s.re)
    (hne : s≠4/3) : AnalyticAt ℂ cubicThetaConstantContinuation s := by
  have hlin : 1<(3*s-2).re := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      zero_mul,sub_zero]
    linarith
  have hnum0 : 3*s-3≠0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      zero_mul,sub_zero,Complex.zero_re] at he
    linarith
  have hnum1 : 3*s-3≠1 := by
    intro hz
    apply hne
    linear_combination (1/3:ℂ)*hz
  have hden0 : 3*s-2≠0 := by
    intro hz
    rw [hz,Complex.zero_re] at hlin
    linarith
  have hden1 : 3*s-2≠1 := by
    intro hz
    rw [hz,Complex.one_re] at hlin
    linarith
  have hZn : AnalyticAt ℂ (fun z : ℂ => principalIdealZeta (3*z-3)) s :=
    (cubicTheta_principalZeta_analyticAt hnum0 hnum1).comp
      (f:=fun z : ℂ => 3*z-3) (x:=s) (by fun_prop)
  have hZd : AnalyticAt ℂ (fun z : ℂ => principalIdealZeta (3*z-2)) s :=
    (cubicTheta_principalZeta_analyticAt hden0 hden1).comp
      (f:=fun z : ℂ => 3*z-2) (x:=s) (by fun_prop)
  change AnalyticAt ℂ (fun z => (2*(3:ℂ)^(3-3*z)/(1-(3:ℂ)^(2-3*z)))*
    principalIdealZeta (3*z-3)/principalIdealZeta (3*z-2)) s
  exact ((((analyticAt_const.mul (cubicThetaRamifiedPower_analytic 3 s)).div
    (analyticAt_const.sub (cubicThetaRamifiedPower_analytic 2 s))
      (cubicThetaScattering_local_denominator hs)).mul hZn).div hZd
        (cubicTheta_principalZeta_right_ne_zero hlin))

end CubicFirstMoment

end

end OAI
