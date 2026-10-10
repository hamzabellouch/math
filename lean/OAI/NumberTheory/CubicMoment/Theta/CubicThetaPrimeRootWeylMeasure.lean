import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylCover

namespace OAI

/-! The actual conjugated inversion preserves the root-cover measure
and the square norm of its sections. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeylImage_fundamental {p : Eisenstein} (hp : primaryPrime p) :
    IsFundamentalDomain (cubicThetaPrimeRootCoverGroup hp)
      ((fun y : CubicThetaPoint => cubicThetaPrimeRootWeylElement hp • y) ''
        cubicThetaPrimeRootCoverDomain hp) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeRootWeylElement hp)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeRootWeylElement hp)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeRootWeylConjugate_involutive hp).toPerm
  intro g y
  change cubicThetaPrimeRootWeylElement hp • ((cubicThetaPrimeRootWeylConjugate hp g).val • y)=
    g.val • (cubicThetaPrimeRootWeylElement hp • y)
  rw [cubicThetaPrimeRootWeylPoint_intertwines,cubicThetaPrimeRootWeylConjugate_involutive]

lemma cubicThetaPrimeRootWeyl_map_restrict {p : Eisenstein} (hp : primaryPrime p)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) :
    (cubicThetaPointMeasure.restrict S).map (fun y : CubicThetaPoint =>
      cubicThetaPrimeRootWeylElement hp • y)=
      cubicThetaPointMeasure.restrict ((fun y : CubicThetaPoint =>
        cubicThetaPrimeRootWeylElement hp • y) '' S) := by
  have hImage := (Homeomorph.smul (cubicThetaPrimeRootWeylElement hp)).measurableEmbedding.measurableSet_image' hS
  change MeasurableSet ((fun y : CubicThetaPoint => cubicThetaPrimeRootWeylElement hp • y) '' S) at hImage
  have he := Measure.restrict_map (measurable_const_smul (cubicThetaPrimeRootWeylElement hp))
    hImage (μ:=cubicThetaPointMeasure)
  rw [(measurePreserving_smul (cubicThetaPrimeRootWeylElement hp) cubicThetaPointMeasure).map_eq] at he
  have hpre : (fun y : CubicThetaPoint => cubicThetaPrimeRootWeylElement hp • y) ⁻¹'
      ((fun y : CubicThetaPoint => cubicThetaPrimeRootWeylElement hp • y) '' S)=S :=
    Set.preimage_image_eq _ (MulAction.injective (cubicThetaPrimeRootWeylElement hp))
  rw [hpre] at he
  exact he.symm

theorem cubicThetaPrimeRootCoverWeyl_measurePreserving {p : Eisenstein} (hp : primaryPrime p) :
    MeasurePreserving (cubicThetaPrimeRootCoverWeyl hp)
      (cubicThetaPrimeRootCoverMeasure hp) (cubicThetaPrimeRootCoverMeasure hp) := by
  have hcont : Continuous (cubicThetaPrimeRootCoverWeyl hp) :=
    (cubicThetaPrimeRootCoverWeylHomeomorph hp).continuous
  refine ⟨hcont.measurable,?_⟩
  calc
    _ = ((cubicThetaPointMeasure.restrict (cubicThetaPrimeRootCoverDomain hp)).map
        (fun y : CubicThetaPoint => cubicThetaPrimeRootWeylElement hp • y)).map
          (cubicThetaPrimeRootCoverMap hp) := by
      rw [cubicThetaPrimeRootCoverMeasure,
        Measure.map_map hcont.measurable (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable,
        Measure.map_map (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable
          (measurable_const_smul (cubicThetaPrimeRootWeylElement hp))]
      rfl
    _ = (cubicThetaPointMeasure.restrict
        ((fun y : CubicThetaPoint => cubicThetaPrimeRootWeylElement hp • y) ''
          cubicThetaPrimeRootCoverDomain hp)).map (cubicThetaPrimeRootCoverMap hp) := by
      rw [cubicThetaPrimeRootWeyl_map_restrict hp (cubicThetaPrimeRootCoverDomain_measurable hp)]
    _ = cubicThetaPrimeRootCoverMeasure hp :=
      (cubicThetaPrimeRootCoverMeasure_independent hp (cubicThetaPrimeRootWeylImage_fundamental hp)).symm

lemma cubicThetaPrimeRootWeylSection_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) (q : CubicThetaPrimeRootCover hp) :
    cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootWeylSection hp F) q=
      cubicThetaPrimeRootSectionNorm hp F (cubicThetaPrimeRootCoverWeyl hp q) := by
  induction q using Quotient.inductionOn with
  | h y => rfl

theorem cubicThetaPrimeRootWeylSection_mass {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) :
    (∫ q, (cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootWeylSection hp F) q)^2
      ∂cubicThetaPrimeRootCoverMeasure hp)=
      ∫ q, (cubicThetaPrimeRootSectionNorm hp F q)^2 ∂cubicThetaPrimeRootCoverMeasure hp := by
  simp_rw [cubicThetaPrimeRootWeylSection_norm]
  exact (cubicThetaPrimeRootCoverWeyl_measurePreserving hp).integral_comp
    (cubicThetaPrimeRootCoverWeylHomeomorph hp).measurableEmbedding
    (fun q => (cubicThetaPrimeRootSectionNorm hp F q)^2)

end CubicFirstMoment

end

end OAI
