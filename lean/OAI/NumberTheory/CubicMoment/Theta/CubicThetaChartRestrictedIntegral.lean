import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalQuotientMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! Scalar integration in an injective quotient chart, for reconstruction
of the global core cutoff norm from its coordinate norm. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaChart_map_restrict
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source) :
    (cubicThetaPointMeasure.restrict S).map cubicThetaQuotientMap=
      cubicThetaQuotientMeasure.restrict (cubicThetaQuotientMap '' S) := by
  ext B hB
  rw [Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hB,
    Measure.restrict_apply (hB.preimage cubicThetaQuotientMap_open.continuous.measurable),
    ← cubicThetaQuotientMeasure_chart e he
      ((hB.preimage cubicThetaQuotientMap_open.continuous.measurable).inter hS)
      (fun _ hx => hSe hx.2),Set.image_preimage_inter,Measure.restrict_apply hB]

lemma cubicThetaChart_integral
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source)
    (f : CubicThetaQuotient → ℝ) (hf : StronglyMeasurable f) :
    (∫ q in cubicThetaQuotientMap '' S, f q ∂cubicThetaQuotientMeasure)=
      ∫ p in S, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure := by
  rw [← cubicThetaChart_map_restrict e he hS hSe]
  exact integral_map_of_stronglyMeasurable cubicThetaQuotientMap_open.continuous.measurable hf

end CubicFirstMoment

end

end OAI
