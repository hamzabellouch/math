import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalResolventWeak

namespace OAI

/-! The constructed global Green operator gives the actual Eisenstein
spectral resolvent initially in Re(s)>2 and at nonreal points of Re(s)>1.
Real poles in (1,2] still require meromorphic continuation. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaGlobalSpectralParameter (s : ℂ) : ℂ := 1-s*(s-2)

lemma cubicThetaGlobalSpectralParameter_regular {s : ℂ} (hs : 1<s.re)
    (h : s.im≠0 ∨ 2<s.re) :
    (cubicThetaGlobalSpectralParameter s).im≠0 ∨
      (cubicThetaGlobalSpectralParameter s).re<1 := by
  by_cases hi : s.im=0
  · right
    have hs2 := h.resolve_left (not_not_intro hi)
    simp only [cubicThetaGlobalSpectralParameter,Complex.sub_re,Complex.one_re,
      Complex.mul_re,Complex.sub_im,hi]
    norm_num
    nlinarith [mul_pos (by linarith : 0<s.re) (by linarith : 0<s.re-2)]
  · left
    simp only [cubicThetaGlobalSpectralParameter,Complex.sub_im,Complex.one_im,
      Complex.mul_im,Complex.sub_re]
    norm_num
    intro he
    have hp : (2*(s.re-1))*s.im=0 := by nlinarith
    exact hi ((mul_eq_zero.mp hp).resolve_left (by linarith))

def cubicThetaGlobalSpectralResolvent (s : ℂ) : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 :=
  cubicThetaGlobalResolvent (cubicThetaGlobalSpectralParameter s)

lemma cubicThetaGlobalSpectralResolvent_analytic {s : ℂ} (hs : 1<s.re)
    (h : s.im≠0 ∨ 2<s.re) : AnalyticAt ℂ cubicThetaGlobalSpectralResolvent s := by
  have hr := cubicThetaGlobalResolvent_analytic (cubicThetaGlobalSpectralParameter_regular hs h)
  have hp : AnalyticAt ℂ cubicThetaGlobalSpectralParameter s :=
    analyticAt_const.sub (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
  exact hr.comp (f:=cubicThetaGlobalSpectralParameter) (x:=s) hp

theorem cubicThetaGlobalSpectralResolvent_weak {s : ℂ} (hs : 1<s.re)
    (h : s.im≠0 ∨ 2<s.re) (F : CubicThetaGlobalL2) (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient v)
        (cubicThetaGlobalEnergyGradient
          (cubicThetaGlobalResolventLift (cubicThetaGlobalSpectralParameter s) F))+
      (s*(s-2))*inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaGlobalSpectralResolvent s F)=
      inner ℂ (cubicThetaGlobalInclusion v) F := by
  have he := cubicThetaGlobalResolventLift_weak (cubicThetaGlobalSpectralParameter_regular hs h) F v
  have hp : 1-cubicThetaGlobalSpectralParameter s=s*(s-2) := by
    unfold cubicThetaGlobalSpectralParameter
    ring
  rw [hp] at he
  exact he

end CubicFirstMoment

end

end OAI
