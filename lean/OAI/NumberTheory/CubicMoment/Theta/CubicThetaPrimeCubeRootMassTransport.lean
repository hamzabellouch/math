import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootDomainMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexPointMeasure

namespace OAI

/-! Fractional translations preserve the literal finite-domain mass
and square integrability of cubic-scale automorphic sections. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootImage_fundamental {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    IsFundamentalDomain (cubicThetaPrimeCubeRootCoverGroup hp)
      ((fun y : CubicThetaPoint => cubicThetaPrimeCubeRootElement hp x • y) ''
        cubicThetaPrimeCubeRootCoverDomain hp) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeCubeRootElement hp x)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeCubeRootElement hp x)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeCubeRootAutomorphism hp (-x)).toEquiv
  intro g y
  change cubicThetaPrimeCubeRootElement hp x • ((cubicThetaPrimeCubeRootConjugate hp (-x) g).val • y)=
    g.val • (cubicThetaPrimeCubeRootElement hp x • y)
  rw [cubicThetaPrimeCubeRootPoint_intertwines,←cubicThetaPrimeCubeRootConjugate_add,
    add_neg_cancel,cubicThetaPrimeCubeRootConjugate_zero]

lemma cubicThetaPrimeCubeRootSection_norm_invariant {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p) (g : cubicThetaPrimeCubeRootCoverGroup hp)
    (x : CubicThetaPoint) : ‖F.val (g • x)‖^2=‖F.val x‖^2 := by
  change ‖F.val (g.val • x)‖^2=‖F.val x‖^2
  have hf : F.val (g.val • x)=cubicThetaKubotaValue g.val*F.val x :=
    F.property (⟨g.val,g.property⟩ : cubicThetaPrimeRootSubgroup (p^3)) x
  rw [hf,norm_mul,cubicThetaKubotaValue_norm,one_mul]

theorem cubicThetaPrimeCubeRootSectionTranslate_mass {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeCubeRootSections p) :
    (∫ y in cubicThetaPrimeCubeRootCoverDomain hp,
      ‖(cubicThetaPrimeCubeRootSectionTranslate hp x F).val y‖^2 ∂cubicThetaPointMeasure)=
        ∫ y in cubicThetaPrimeCubeRootCoverDomain hp,‖F.val y‖^2 ∂cubicThetaPointMeasure := by
  have hi := (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (f:=fun y : CubicThetaPoint => ‖F.val y‖^2)
    (cubicThetaPrimeCubeRootImage_fundamental hp x) (cubicThetaPrimeCubeRootSection_norm_invariant hp F)
  have hc := (measurePreserving_smul (cubicThetaPrimeCubeRootElement hp x) cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeRootElement hp x))
      (fun y => ‖F.val y‖^2) (cubicThetaPrimeCubeRootCoverDomain hp)
  exact (hi.trans hc).symm

theorem cubicThetaPrimeCubeRootSectionTranslate_memLp {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeCubeRootSections p)
    (hF : MemLp F.val 2 (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp))) :
    MemLp (cubicThetaPrimeCubeRootSectionTranslate hp x F).val 2
      (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp)) := by
  have hf := (memLp_two_iff_integrable_sq_norm F.val.continuous.aestronglyMeasurable).mp hF
  have hi := (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).integrableOn_iff
    (f:=fun y : CubicThetaPoint => ‖F.val y‖^2)
    (cubicThetaPrimeCubeRootImage_fundamental hp x) (cubicThetaPrimeCubeRootSection_norm_invariant hp F)
  have hImage := hi.mp hf
  apply (memLp_two_iff_integrable_sq_norm
    (cubicThetaPrimeCubeRootSectionTranslate hp x F).val.continuous.aestronglyMeasurable).mpr
  exact ((measurePreserving_smul (cubicThetaPrimeCubeRootElement hp x) cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeRootElement hp x))).mp hImage

end CubicFirstMoment

end

end OAI
