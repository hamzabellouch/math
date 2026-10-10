import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCoverAtkin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCoverMeasure

namespace OAI

/-! The prime normalizer preserves the actual measure on the finite
arithmetic cover. The proof transports the constructed fundamental domain. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeAtkinImage_fundamental {p : Eisenstein} (hp : primaryPrime p) :
    IsFundamentalDomain (cubicThetaPrimeCoverGroup hp)
      ((fun x : CubicThetaPoint => cubicThetaPrimeAtkinMatrix hp • x) ''
        cubicThetaPrimeCoverDomain hp) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeAtkinMatrix hp)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeAtkinMatrix hp)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeCoverAtkinEquiv hp)
  intro g x
  change cubicThetaPrimeAtkinMatrix hp • (cubicThetaPrimeCoverAtkinEquiv hp g • x)=
    g • (cubicThetaPrimeAtkinMatrix hp • x)
  rw [cubicThetaPrimeCoverAtkin_intertwines,cubicThetaPrimeCoverAtkinEquiv_involutive]

lemma cubicThetaPrimeAtkin_map_restrict {p : Eisenstein} (hp : primaryPrime p)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) :
    (cubicThetaPointMeasure.restrict S).map (fun x : CubicThetaPoint =>
      cubicThetaPrimeAtkinMatrix hp • x)=
      cubicThetaPointMeasure.restrict ((fun x : CubicThetaPoint =>
        cubicThetaPrimeAtkinMatrix hp • x) '' S) := by
  have hImage := (Homeomorph.smul (cubicThetaPrimeAtkinMatrix hp)).measurableEmbedding.measurableSet_image' hS
  change MeasurableSet ((fun x : CubicThetaPoint => cubicThetaPrimeAtkinMatrix hp • x) '' S) at hImage
  have he := Measure.restrict_map (measurable_const_smul (cubicThetaPrimeAtkinMatrix hp))
    hImage (μ:=cubicThetaPointMeasure)
  rw [(measurePreserving_smul (cubicThetaPrimeAtkinMatrix hp) cubicThetaPointMeasure).map_eq] at he
  have hpre : (fun x : CubicThetaPoint => cubicThetaPrimeAtkinMatrix hp • x) ⁻¹'
      ((fun x : CubicThetaPoint => cubicThetaPrimeAtkinMatrix hp • x) '' S)=S :=
    Set.preimage_image_eq _ (MulAction.injective (cubicThetaPrimeAtkinMatrix hp))
  rw [hpre] at he
  exact he.symm

theorem cubicThetaPrimeCoverAtkin_measurePreserving {p : Eisenstein} (hp : primaryPrime p) :
    MeasurePreserving (cubicThetaPrimeCoverAtkinMap hp)
      (cubicThetaPrimeCoverMeasure hp) (cubicThetaPrimeCoverMeasure hp) := by
  have hcont : Continuous (cubicThetaPrimeCoverAtkinMap hp) :=
    (cubicThetaPrimeCoverAtkinHomeomorph hp).continuous
  refine ⟨hcont.measurable,?_⟩
  calc
    _ = ((cubicThetaPointMeasure.restrict (cubicThetaPrimeCoverDomain hp)).map
        (fun x : CubicThetaPoint => cubicThetaPrimeAtkinMatrix hp • x)).map
          (cubicThetaPrimeCoverMap hp) := by
      rw [cubicThetaPrimeCoverMeasure,
        Measure.map_map hcont.measurable
          (cubicThetaPrimeCoverMap_open hp).continuous.measurable,
        Measure.map_map (cubicThetaPrimeCoverMap_open hp).continuous.measurable
          (measurable_const_smul (cubicThetaPrimeAtkinMatrix hp))]
      rfl
    _ = (cubicThetaPointMeasure.restrict
        ((fun x : CubicThetaPoint => cubicThetaPrimeAtkinMatrix hp • x) ''
          cubicThetaPrimeCoverDomain hp)).map (cubicThetaPrimeCoverMap hp) := by
      rw [cubicThetaPrimeAtkin_map_restrict hp (cubicThetaPrimeCoverDomain_measurable hp)]
    _ = cubicThetaPrimeCoverMeasure hp :=
      (cubicThetaPrimeCoverMeasure_independent hp (cubicThetaPrimeAtkinImage_fundamental hp)).symm

end CubicFirstMoment

end

end OAI
