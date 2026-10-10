import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramDenominatorIntegral

namespace OAI

/-! Joint continuity of the weighted inversion kernel at positive height. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaGramJointKernel (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    (c : ℂ) (y : ℂ × ℝ) : ℂ :=
  star (W y.2)/(y.2:ℂ)^3*cubicThetaGramInversionKernel h k V c y.1 y.2

lemma cubicThetaInversion_continuousAt {c : ℂ} (hc : c≠0)
    {y : ℂ × ℝ} (hy : 0<y.2) : ContinuousAt (cubicThetaInversion c) y := by
  have hR : cubicThetaRadius y≠0 := (cubicThetaRadius_pos hy).ne'
  have hN : Complex.normSq c≠0 := (Complex.normSq_pos.mpr hc).ne'
  have hRC : (cubicThetaRadius y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hR
  unfold cubicThetaInversion cubicThetaRadius at *
  fun_prop (disch := first | assumption | exact mul_ne_zero (pow_ne_zero _ hc) hRC |
    exact mul_ne_zero hN hR)

lemma cubicThetaGramJointKernel_continuousAt (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    {c : ℂ} (hc : c≠0) {y : ℂ × ℝ} (hy : 0<y.2) :
    ContinuousAt (cubicThetaGramJointKernel h k W V c) y := by
  have hm := cubicThetaInversion_continuousAt hc hy
  have hz : (y.2:ℂ)^3≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hy.ne')
  unfold cubicThetaGramJointKernel cubicThetaGramInversionKernel
  exact ((W.continuous.continuousAt.comp continuous_snd.continuousAt).star.div
    ((Complex.continuous_ofReal.comp continuous_snd).continuousAt.pow 3) hz).mul
      ((((cubicThetaHorizontalCharacter_contDiff h).continuous.continuousAt.comp
        continuous_fst.continuousAt).star.mul (V.continuous.continuousAt.comp hm.snd)).mul
          ((cubicThetaHorizontalCharacter_contDiff k).continuous.continuousAt.comp hm.fst))

end CubicFirstMoment

end

end OAI
