import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierTranslation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalCompact

namespace OAI

/-! Absolute integrability of the actual weighted cell coefficients. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalCharacter_continuous (h : Eisenstein) :
    Continuous (cubicThetaHorizontalCharacter h) := by
  unfold cubicThetaHorizontalCharacter
  apply continuous_subtype_val.comp
  apply Real.continuous_fourierChar.comp
  unfold tracePair
  fun_prop

lemma cubicThetaHorizontalFourier_integrable (h : Eisenstein) (f : ℂ → ℂ)
    (hf : Continuous f) :
    IntegrableOn (fun z => star (cubicThetaHorizontalCharacter h z)*f z)
      cubicThetaHorizontalCell := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  exact (((cubicThetaHorizontalCharacter_continuous h).star.mul hf).continuousOn.integrableOn_compact hK).mono_set hsub

end CubicFirstMoment

end

end OAI
