import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotientMeasure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFundamentalExtension

namespace OAI

/-! On an injective quotient chart, hyperbolic measure downstairs equals
hyperbolic measure upstairs. This follows by replacing the fundamental
domain with the proved measurable extension of that chart. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaQuotientMeasure_local_image {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hQ : MeasurableSet (cubicThetaQuotientMap '' S))
    (hi : InjOn cubicThetaQuotientMap S) :
    cubicThetaQuotientMeasure (cubicThetaQuotientMap '' S)=cubicThetaPointMeasure S := by
  rw [cubicThetaQuotientMeasure_independent
    (cubicThetaFundamentalExtension_isFundamentalDomain hS hQ hi cubicThetaPointMeasure),
    Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hQ,
    Measure.restrict_apply (hQ.preimage cubicThetaQuotientMap_open.continuous.measurable),
    cubicThetaFundamentalExtension_inter]

lemma cubicThetaQuotientChart_measurable_image
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source) :
    MeasurableSet (cubicThetaQuotientMap '' S) := by
  have ht := e.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image'
    (hS.preimage (measurable_subtype_coe : Measurable (Subtype.val : e.source → CubicThetaPoint)))
  convert ht using 1
  ext q
  constructor
  · rintro ⟨p,hp,hpq⟩
    exact ⟨⟨p,hSe hp⟩,hp,(congrFun he p).trans hpq⟩
  · rintro ⟨p,hp,hpq⟩
    exact ⟨p.val,hp,(congrFun he p.val).symm.trans hpq⟩

lemma cubicThetaQuotientMeasure_chart
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source) :
    cubicThetaQuotientMeasure (cubicThetaQuotientMap '' S)=cubicThetaPointMeasure S := by
  apply cubicThetaQuotientMeasure_local_image hS
    (cubicThetaQuotientChart_measurable_image e he hS hSe)
  intro p hp q hq hpq
  apply e.injOn (hSe hp) (hSe hq)
  simpa only [he] using hpq

end CubicFirstMoment

end

end OAI
