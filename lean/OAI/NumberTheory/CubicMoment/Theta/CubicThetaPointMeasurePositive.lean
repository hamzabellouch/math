import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateIntegral
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

/-! The actual hyperbolic measure is positive on every nonempty open
subset of the positive-height space. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

instance cubicThetaPointMeasure_openPositive :
    Measure.IsOpenPosMeasure cubicThetaPointMeasure where
  open_pos U hU hne := by
    have hopen : IsOpen (cubicThetaPointCoordinates '' U) :=
      (isOpen_lt continuous_const continuous_snd).isOpenEmbedding_subtypeVal.isOpenMap U hU
    have he : {y : ℂ × ℝ | cubicThetaHyperbolicDensity y≠0} ∩
        (cubicThetaPointCoordinates '' U)=cubicThetaPointCoordinates '' U := by
      apply inter_eq_right.mpr
      rintro y ⟨p,hp,rfl⟩
      change ENNReal.ofReal ((p.val.2^3)⁻¹)≠0
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos p.property 3)))
    rw [cubicThetaPointMeasure_apply hU.measurableSet,cubicThetaHyperbolicMeasure]
    intro hz
    have hh := (withDensity_apply_eq_zero (μ:=(volume : Measure (ℂ × ℝ)))
      (s:=cubicThetaPointCoordinates '' U) cubicThetaHyperbolicDensity_measurable).mp hz
    rw [he] at hh
    exact hopen.measure_ne_zero volume (hne.image _) hh

end CubicFirstMoment

end

end OAI
