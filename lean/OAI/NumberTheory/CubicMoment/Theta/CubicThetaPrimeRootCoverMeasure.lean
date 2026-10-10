import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootCoverDomain

namespace OAI

/-! Independence of the fractional-root cover measure from the finite translated
fundamental domain used in its construction. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

instance cubicThetaPrimeRootCoverPointMeasure_invariant {p : Eisenstein} (hp : primaryPrime p) :
    SMulInvariantMeasure (cubicThetaPrimeRootCoverGroup hp) CubicThetaPoint cubicThetaPointMeasure where
  measure_preimage_smul g _S hS :=
    SMulInvariantMeasure.measure_preimage_smul (g.val : cubicThetaPrincipalGroup) hS

lemma cubicThetaPrimeRootCoverMeasure_apply {p : Eisenstein} (hp : primaryPrime p)
    {S : Set (CubicThetaPrimeRootCover hp)} (hS : MeasurableSet S) :
    cubicThetaPrimeRootCoverMeasure hp S=
      cubicThetaPointMeasure ((cubicThetaPrimeRootCoverMap hp) ⁻¹' S ∩ cubicThetaPrimeRootCoverDomain hp) := by
  rw [cubicThetaPrimeRootCoverMeasure,Measure.map_apply
    (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable hS,
    Measure.restrict_apply (hS.preimage (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable)]

theorem cubicThetaPrimeRootCoverMeasure_independent {p : Eisenstein} (hp : primaryPrime p)
    {D : Set CubicThetaPoint}
    (hD : IsFundamentalDomain (cubicThetaPrimeRootCoverGroup hp) D cubicThetaPointMeasure) :
    cubicThetaPrimeRootCoverMeasure hp=
      (cubicThetaPointMeasure.restrict D).map (cubicThetaPrimeRootCoverMap hp) := by
  ext S hS
  rw [cubicThetaPrimeRootCoverMeasure_apply hp hS,Measure.map_apply
    (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable hS,
    Measure.restrict_apply (hS.preimage (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable)]
  apply (cubicThetaPrimeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).measure_set_eq hD
    (hS.preimage (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable)
  intro g
  ext x
  simp only [mem_preimage,(cubicThetaPrimeRootCover_covering hp).map_smul]

end CubicFirstMoment

end

end OAI
