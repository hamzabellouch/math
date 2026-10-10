import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCoverDomain

namespace OAI

/-! Independence of the prime-cover measure from the finite translated
fundamental domain used in its construction. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

instance cubicThetaPrimeCoverPointMeasure_invariant {p : Eisenstein} (hp : primaryPrime p) :
    SMulInvariantMeasure (cubicThetaPrimeCoverGroup hp) CubicThetaPoint cubicThetaPointMeasure where
  measure_preimage_smul g _S hS :=
    SMulInvariantMeasure.measure_preimage_smul (g.val : cubicThetaPrincipalGroup) hS

lemma cubicThetaPrimeCoverMeasure_apply {p : Eisenstein} (hp : primaryPrime p)
    {S : Set (CubicThetaPrimeCover hp)} (hS : MeasurableSet S) :
    cubicThetaPrimeCoverMeasure hp S=
      cubicThetaPointMeasure ((cubicThetaPrimeCoverMap hp) ⁻¹' S ∩ cubicThetaPrimeCoverDomain hp) := by
  rw [cubicThetaPrimeCoverMeasure,Measure.map_apply
    (cubicThetaPrimeCoverMap_open hp).continuous.measurable hS,
    Measure.restrict_apply (hS.preimage (cubicThetaPrimeCoverMap_open hp).continuous.measurable)]

theorem cubicThetaPrimeCoverMeasure_independent {p : Eisenstein} (hp : primaryPrime p)
    {D : Set CubicThetaPoint}
    (hD : IsFundamentalDomain (cubicThetaPrimeCoverGroup hp) D cubicThetaPointMeasure) :
    cubicThetaPrimeCoverMeasure hp=
      (cubicThetaPointMeasure.restrict D).map (cubicThetaPrimeCoverMap hp) := by
  ext S hS
  rw [cubicThetaPrimeCoverMeasure_apply hp hS,Measure.map_apply
    (cubicThetaPrimeCoverMap_open hp).continuous.measurable hS,
    Measure.restrict_apply (hS.preimage (cubicThetaPrimeCoverMap_open hp).continuous.measurable)]
  apply (cubicThetaPrimeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).measure_set_eq hD
    (hS.preimage (cubicThetaPrimeCoverMap_open hp).continuous.measurable)
  intro g
  ext x
  simp only [mem_preimage,(cubicThetaPrimeCover_covering hp).map_smul]

end CubicFirstMoment

end

end OAI
