import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspFourierIntegral

namespace OAI

/-! Normalization of the actual weighted arithmetic Fourier coefficient. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaFourierRadialTest (h : Eisenstein) (W : C_c(ℝ,ℂ)) (s : ℂ) : ℂ :=
  ∫ v in Ioi (2:ℝ), star (W v)*(v:ℂ)^s*
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)/(v:ℂ)^3

lemma cubicThetaPeriod_fourier_constant :
    ((9*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(9*Real.sqrt 3):ℂ)=(Real.pi:ℂ) := by
  have hr : (Real.sqrt 3:ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<3))
  push_cast
  field_simp

theorem cubicThetaCuspFourierObservable_normalized {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {s : ℂ} (hs : 3<s.re) :
    cubicThetaCuspFourierObservable h W s=
      ((Real.pi:ℂ)/Complex.Gamma s)*cubicThetaFrequencyDirichlet h s*
        cubicThetaFourierRadialTest h W s := by
  rw [cubicThetaCuspFourierObservable_coefficient hh W hs,cubicThetaFourierRadialTest,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  have hphase : (Real.fourierChar (tracePair 0 (cubicThetaRowFrequency h)):ℂ)=1 := by
    simp [tracePair]
  simp only [cubicThetaNonzeroFrequencyTerm,ite_eq_right hh,hphase,mul_one,Complex.real_smul]
  calc
    _ = (((9*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(9*Real.sqrt 3):ℂ))*
        (star (W v)*(v:ℂ)^s*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)/(v:ℂ)^3)/
            Complex.Gamma s*cubicThetaFrequencyDirichlet h s := by ring
    _ = _ := by rw [cubicThetaPeriod_fourier_constant]; ring

end CubicFirstMoment

end

end OAI
