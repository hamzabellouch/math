import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspFourierObservable
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStripFubini
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticTorus

namespace OAI

/-! Absolutely convergent evaluation of the genuine weighted cusp observations. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaCuspFourier_integrable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 3<s.re) :
    IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
        cubicThetaArithmeticRemainder p.val s)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaCuspFourierTest h W) (cubicThetaForcedCusp s)
  apply hi.congr
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
    cubicThetaForcedCusp_coe hs] with p hp hR
  change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p) _=_
  rw [hp,hR,RCLike.inner_apply]
  simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
  ring

lemma cubicThetaCuspFourierObservable_iterated (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 3<s.re) :
    cubicThetaCuspFourierObservable h W s=
      ∫ v in Ioi (2:ℝ), star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
            cubicThetaArithmeticRemainder (z,v) s := by
  rw [cubicThetaCuspFourierObservable_right h W hs]
  have hf := cubicThetaCuspStrip_fubini
    (fun y => star (W y.2*(Real.fourierChar (tracePair y.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaArithmeticRemainder y s) (cubicThetaCuspFourier_integrable h W hs)
  change (∫ p in cubicThetaCuspStrip 2,
    star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaArithmeticRemainder p.val s ∂cubicThetaPointMeasure)=_ at hf
  rw [hf]
  apply integral_congr_ae
  filter_upwards with v
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  simp only [star_mul]
  ring

lemma cubicThetaCuspFourierObservable_coefficient {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {s : ℂ} (hs : 3<s.re) :
    cubicThetaCuspFourierObservable h W s=
      ∫ v in Ioi (2:ℝ), star (W v)/(v:ℂ)^3*
        ((9*Real.sqrt 3/2:ℝ) •
          (((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
            cubicThetaNonzeroFrequencyTerm (0,v) s h)) := by
  rw [cubicThetaCuspFourierObservable_iterated h W hs]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [cubicThetaArithmetic_horizontal_coefficient hv.le (by linarith) hh]

end CubicFirstMoment

end

end OAI
