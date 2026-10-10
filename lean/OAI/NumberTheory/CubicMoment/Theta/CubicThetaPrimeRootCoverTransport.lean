import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootCoverAction

namespace OAI

/-! The actual fractional roots preserve hyperbolic measure on their
finite arithmetic cover, by transport of the proved fundamental domain. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootImage_fundamental {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    IsFundamentalDomain (cubicThetaPrimeRootCoverGroup hp)
      ((fun y : CubicThetaPoint => cubicThetaPrimeRootElement hp x • y) ''
        cubicThetaPrimeRootCoverDomain hp) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeRootElement hp x)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeRootElement hp x)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeRootAutomorphism hp (-x)).toEquiv
  intro g y
  change cubicThetaPrimeRootElement hp x • ((cubicThetaPrimeRootConjugate hp (-x) g).val • y)=
    g.val • (cubicThetaPrimeRootElement hp x • y)
  rw [cubicThetaPrimeRootPoint_intertwines,←cubicThetaPrimeRootConjugate_add,
    add_neg_cancel,cubicThetaPrimeRootConjugate_zero]

lemma cubicThetaPrimeRoot_map_restrict {p : Eisenstein} (hp : primaryPrime p) (x : Eisenstein)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) :
    (cubicThetaPointMeasure.restrict S).map (fun y : CubicThetaPoint =>
      cubicThetaPrimeRootElement hp x • y)=
      cubicThetaPointMeasure.restrict ((fun y : CubicThetaPoint =>
        cubicThetaPrimeRootElement hp x • y) '' S) := by
  have hImage := (Homeomorph.smul (cubicThetaPrimeRootElement hp x)).measurableEmbedding.measurableSet_image' hS
  change MeasurableSet ((fun y : CubicThetaPoint => cubicThetaPrimeRootElement hp x • y) '' S) at hImage
  have he := Measure.restrict_map (measurable_const_smul (cubicThetaPrimeRootElement hp x))
    hImage (μ:=cubicThetaPointMeasure)
  rw [(measurePreserving_smul (cubicThetaPrimeRootElement hp x) cubicThetaPointMeasure).map_eq] at he
  have hpre : (fun y : CubicThetaPoint => cubicThetaPrimeRootElement hp x • y) ⁻¹'
      ((fun y : CubicThetaPoint => cubicThetaPrimeRootElement hp x • y) '' S)=S :=
    Set.preimage_image_eq _ (MulAction.injective (cubicThetaPrimeRootElement hp x))
  rw [hpre] at he
  exact he.symm

theorem cubicThetaPrimeRootCoverTranslate_measurePreserving {p : Eisenstein} (hp : primaryPrime p) (x : Eisenstein) :
    MeasurePreserving (cubicThetaPrimeRootCoverTranslate hp x)
      (cubicThetaPrimeRootCoverMeasure hp) (cubicThetaPrimeRootCoverMeasure hp) := by
  have hcont : Continuous (cubicThetaPrimeRootCoverTranslate hp x) :=
    (cubicThetaPrimeRootCoverHomeomorph hp x).continuous
  refine ⟨hcont.measurable,?_⟩
  calc
    _ = ((cubicThetaPointMeasure.restrict (cubicThetaPrimeRootCoverDomain hp)).map
        (fun y : CubicThetaPoint => cubicThetaPrimeRootElement hp x • y)).map
          (cubicThetaPrimeRootCoverMap hp) := by
      rw [cubicThetaPrimeRootCoverMeasure,
        Measure.map_map hcont.measurable
          (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable,
        Measure.map_map (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable
          (measurable_const_smul (cubicThetaPrimeRootElement hp x))]
      rfl
    _ = (cubicThetaPointMeasure.restrict
        ((fun y : CubicThetaPoint => cubicThetaPrimeRootElement hp x • y) ''
          cubicThetaPrimeRootCoverDomain hp)).map (cubicThetaPrimeRootCoverMap hp) := by
      rw [cubicThetaPrimeRoot_map_restrict hp x (cubicThetaPrimeRootCoverDomain_measurable hp)]
    _ = cubicThetaPrimeRootCoverMeasure hp :=
      (cubicThetaPrimeRootCoverMeasure_independent hp (cubicThetaPrimeRootImage_fundamental hp x)).symm

end CubicFirstMoment

end

end OAI
