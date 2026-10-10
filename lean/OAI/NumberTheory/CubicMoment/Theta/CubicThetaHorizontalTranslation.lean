import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalDomain

namespace OAI

/-! Integration of a level-three periodic function is independent of
horizontal translation, on the actual half-open Eisenstein cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalTranslated_fundamental (a : ℂ) :
    IsFundamentalDomain CubicThetaPeriodGroup
      ((fun z : ℂ => z+a) '' cubicThetaHorizontalCell) volume := by
  apply (cubicThetaHorizontalCell_fundamental volume).image_of_equiv
    (Homeomorph.addRight a).toEquiv
    (measurePreserving_add_right volume (-a)).quasiMeasurePreserving
    (Equiv.refl CubicThetaPeriodGroup)
  intro g z
  change (z+3*((Multiplicative.toAdd g:Eisenstein):ℂ))+a=(z+a)+3*((Multiplicative.toAdd g:Eisenstein):ℂ)
  ring

lemma cubicThetaHorizontal_translate_integral (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) (a : ℂ) :
    (∫ z in cubicThetaHorizontalCell,f (z+a))=∫ z in cubicThetaHorizontalCell,f z := by
  have hi (g : CubicThetaPeriodGroup) (z : ℂ) : f (g • z)=f z := hf (Multiplicative.toAdd g) z
  have he := (cubicThetaHorizontalCell_fundamental volume).setIntegral_eq
    (cubicThetaHorizontalTranslated_fundamental a) hi
  have hc := (measurePreserving_add_right volume a).setIntegral_image_emb
    (Homeomorph.addRight a).measurableEmbedding f cubicThetaHorizontalCell
  exact (he.trans hc).symm

lemma cubicThetaHorizontal_translate_integrable (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) (a : ℂ)
    (hi : IntegrableOn f cubicThetaHorizontalCell) :
    IntegrableOn (fun z => f (z+a)) cubicThetaHorizontalCell := by
  have hperiod (g : CubicThetaPeriodGroup) (z : ℂ) : f (g • z)=f z := hf (Multiplicative.toAdd g) z
  have he := ((cubicThetaHorizontalCell_fundamental volume).integrableOn_iff
    (cubicThetaHorizontalTranslated_fundamental a) hperiod).mp hi
  exact ((measurePreserving_add_right volume a).integrableOn_image
    (Homeomorph.addRight a).measurableEmbedding).mp he

end CubicFirstMoment

end

end OAI
