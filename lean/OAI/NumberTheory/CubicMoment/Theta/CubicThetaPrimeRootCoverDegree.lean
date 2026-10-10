import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootCoverMeasure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCoverDegree

namespace OAI

/-! The root cover has its exact finite subgroup index as measure degree. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

def cubicThetaPrimeRootCoverProjection {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPrimeRootCover hp → CubicThetaQuotient :=
  Quotient.map id (by
    intro a b hab
    obtain ⟨g,hg⟩ := hab
    exact ⟨g.val,hg⟩)

lemma cubicThetaPrimeRootCoverProjection_apply {p : Eisenstein} (hp : primaryPrime p)
    (y : CubicThetaPoint) :
    cubicThetaPrimeRootCoverProjection hp (cubicThetaPrimeRootCoverMap hp y)=
      cubicThetaQuotientMap y := rfl

lemma cubicThetaPrimeRootCoverProjection_continuous {p : Eisenstein} (hp : primaryPrime p) :
    Continuous (cubicThetaPrimeRootCoverProjection hp) := by
  apply (cubicThetaPrimeRootCoverMap_open hp).isQuotientMap.continuous_iff.mpr
  exact cubicThetaQuotientMap_open.continuous

theorem cubicThetaPrimeRootCoverProjection_measure {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeRootCoverMeasure hp).map (cubicThetaPrimeRootCoverProjection hp)=
      ((cubicThetaPrimeRootCoverGroup hp).index : ℝ≥0∞) • cubicThetaQuotientMeasure := by
  let : Fintype (cubicThetaPrimeRootTransversal hp) := Fintype.ofFinite _
  have hdis : Pairwise (fun t u : cubicThetaPrimeRootTransversal hp =>
      Disjoint ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
        ((fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain)) := by
    intro t u htu
    exact cubicThetaFundamentalDomain_translates_disjoint
      (fun he => htu (Subtype.ext he))
  have hmeas (t : cubicThetaPrimeRootTransversal hp) :
      MeasurableSet ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain) :=
    (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image'
      cubicThetaFundamentalDomain_measurable
  rw [cubicThetaPrimeRootCoverMeasure,
    Measure.map_map (cubicThetaPrimeRootCoverProjection_continuous hp).measurable
      (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable]
  change (cubicThetaPointMeasure.restrict (⋃ t : cubicThetaPrimeRootTransversal hp,
    (fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)).map
      cubicThetaQuotientMap=_
  rw [Measure.restrict_iUnion hdis hmeas,
    Measure.map_sum cubicThetaQuotientMap_open.continuous.measurable.aemeasurable]
  simp_rw [cubicThetaFundamentalDomain_translate_map]
  ext S hS
  rw [Measure.sum_apply _ hS,Measure.smul_apply,tsum_fintype,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  rw [←Nat.card_eq_fintype_card,(cubicThetaPrimeRootTransversal_complement hp).card_right]
  rfl

end CubicFirstMoment

end

end OAI
