import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramKloostermanFourier

namespace OAI

/-! The complete positive-height Gram kernel, with a finite denominator
sum and no analytic input. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

def cubicThetaKloostermanGram (h k : Eisenstein) (W V : C_c(ℝ,ℂ)) (ε δ : ℝ) : ℂ :=
  ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
    (V v*cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter k)+
      ∑ c∈cubicThetaGramDenominators ε δ,cubicThetaGramKloostermanTerm h k V c v)

theorem cubicThetaPositiveGram_kloosterman (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (V : ℝ → ℂ)) {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hW : ∀ v≤ε,W v=0) (hV : ∀ v≤δ,V v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
      (cubicThetaPositiveFourierProfileL2 k V hδ hV)=
      cubicThetaKloostermanGram h k W V ε δ := by
  rw [cubicThetaPositiveFourierProfileL2,cubicThetaPositiveFourierProfileL2,
    cubicThetaSectionPairing_L2,cubicThetaPositiveFourierProfile_pairing_radial]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only [cubicThetaKloostermanGram]
  congr 1
  have he : (fun z => cubicThetaSectionFunction (cubicThetaPositiveFourierProfileSection k V hδ hV) (z,v))=
      (fun z => cubicThetaFourierProfileSeries k (z,v) V) := by
    funext z
    exact cubicThetaSectionFunction_coordinates
      (cubicThetaPositiveFourierProfileSection k V hδ hV) ⟨(z,v),hε.trans hv⟩
  unfold cubicThetaSectionFourierFunction
  rw [he]
  exact cubicThetaPositiveProfile_fourier_kloosterman h k V hsm hε hδ hV hv.le

end CubicFirstMoment

end

end OAI
