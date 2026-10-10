import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootWeylSections
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootMassTransport

namespace OAI

/-! The opposite cubic root preserves the actual finite-domain norm. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment


lemma cubicThetaPrimeCubeRootWeylImage_fundamental {p : Eisenstein} (hp : primaryPrime p)
    :
    IsFundamentalDomain (cubicThetaPrimeCubeRootCoverGroup hp)
      ((fun y : CubicThetaPoint => cubicThetaPrimeCubeRootWeylElement hp • y) ''
        cubicThetaPrimeCubeRootCoverDomain hp) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeCubeRootWeylElement hp)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeCubeRootWeylElement hp)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeCubeRootWeylConjugate_involutive hp).toPerm
  intro g y
  change cubicThetaPrimeCubeRootWeylElement hp • ((cubicThetaPrimeCubeRootWeylConjugate hp g).val • y)=
    g.val • (cubicThetaPrimeCubeRootWeylElement hp • y)
  rw [cubicThetaPrimeCubeRootWeylPoint_intertwines,cubicThetaPrimeCubeRootWeylConjugate_involutive]

theorem cubicThetaPrimeCubeRootWeylSection_mass {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p) :
    (∫ y in cubicThetaPrimeCubeRootCoverDomain hp,
      ‖(cubicThetaPrimeCubeRootWeylSection hp F).val y‖^2 ∂cubicThetaPointMeasure)=
        ∫ y in cubicThetaPrimeCubeRootCoverDomain hp,‖F.val y‖^2 ∂cubicThetaPointMeasure := by
  have hi := (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (f:=fun y : CubicThetaPoint => ‖F.val y‖^2)
    (cubicThetaPrimeCubeRootWeylImage_fundamental hp) (cubicThetaPrimeCubeRootSection_norm_invariant hp F)
  have hc := (measurePreserving_smul (cubicThetaPrimeCubeRootWeylElement hp) cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeRootWeylElement hp))
      (fun y => ‖F.val y‖^2) (cubicThetaPrimeCubeRootCoverDomain hp)
  exact (hi.trans hc).symm

theorem cubicThetaPrimeCubeRootWeylSection_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p)
    (hF : MemLp F.val 2 (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp))) :
    MemLp (cubicThetaPrimeCubeRootWeylSection hp F).val 2
      (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp)) := by
  have hf := (memLp_two_iff_integrable_sq_norm F.val.continuous.aestronglyMeasurable).mp hF
  have hi := (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).integrableOn_iff
    (f:=fun y : CubicThetaPoint => ‖F.val y‖^2)
    (cubicThetaPrimeCubeRootWeylImage_fundamental hp) (cubicThetaPrimeCubeRootSection_norm_invariant hp F)
  have hImage := hi.mp hf
  apply (memLp_two_iff_integrable_sq_norm
    (cubicThetaPrimeCubeRootWeylSection hp F).val.continuous.aestronglyMeasurable).mpr
  exact ((measurePreserving_smul (cubicThetaPrimeCubeRootWeylElement hp) cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeRootWeylElement hp))).mp hImage


end CubicFirstMoment

end

end OAI
