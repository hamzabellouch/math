import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexIntegrability
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStripMeasure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalCompact

namespace OAI

/-! Fubini on the literal half-open cusp cell, with the v^-3 density. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCuspStrip_fubini (f : ℂ × ℝ → ℂ)
    (hf : IntegrableOn (fun p => f (cubicThetaPointCoordinates p))
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure) :
    (∫ p in cubicThetaCuspStrip 2, f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=
      ∫ v in Ioi (2:ℝ), ∫ z in cubicThetaHorizontalCell, f (z,v)/(v:ℂ)^3 := by
  have hi := (cubicThetaPointIntegrable_complex_density (cubicThetaCuspStrip_measurable 2) f).mp hf
  rw [cubicThetaPointIntegral_complex_density (cubicThetaCuspStrip_measurable 2),
    cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2)]
  rw [cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2)] at hi
  change Integrable (fun y : ℂ × ℝ => f y/(y.2:ℂ)^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict _) at hi
  rw [← Measure.prod_restrict] at hi
  change (∫ y : ℂ × ℝ, f y/(y.2:ℂ)^3 ∂
    ((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ)))=_
  rw [← Measure.prod_restrict]
  exact integral_prod_symm _ hi

end CubicFirstMoment

end

end OAI
