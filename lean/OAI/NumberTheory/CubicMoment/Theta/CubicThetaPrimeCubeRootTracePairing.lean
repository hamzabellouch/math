import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootDilationL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeMassOperator

namespace OAI

/-! The literal cubed-prime trace pairing transported to the actual
common root cover. All degree factors remain explicit. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootFinite_pairing {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeCubeRootFiniteSections hp) :
    inner ℂ (cubicThetaPrimeCubeRootFiniteEmbedding hp F) (cubicThetaPrimeCubeRootFiniteEmbedding hp G)=
      ∫ x in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val.val x)*G.val.val x ∂cubicThetaPointMeasure := by
  change inner ℂ (F.property.toLp F.val.val) (G.property.toLp G.val.val)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [F.property.coeFn_toLp,G.property.coeFn_toLp] with x hF hG
  rw [hF,hG]
  exact RCLike.inner_apply' _ _

theorem cubicThetaPrimeCubeRootTrace_integral {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure)
    (hG : IntegrableOn (fun x => ‖G.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,
      star (F.val x)*(cubicThetaPrimeCubeDilationSection hp G).val x ∂cubicThetaPointMeasure)=
      ((cubicThetaPrimeCubeRootHeckeSubgroup hp).index:ℝ) •
        ∫ x in cubicThetaFundamentalDomain,
          star (F.val x)*(cubicThetaPrimeCubeHecke hp G).val x ∂cubicThetaPointMeasure := by
  have hcF := cubicThetaPrimeCubeInvariant_integrable hp hF (cubicThetaOriginal_norm_invariant F)
  have hcG := cubicThetaPrimeCubeDilation_integrable hp G hG
  have hpair := cubicThetaSquareIntegrablePair F.val (cubicThetaPrimeCubeDilationSection hp G).val
    F.val.continuous (cubicThetaPrimeCubeDilationSection hp G).val.continuous hcF hcG
  rw [cubicThetaPrimeCubeRootHecke_integral hp hpair
    (cubicThetaPrimeCubePair_invariant (cubicThetaPrimeCubeSectionRestrict F)
      (cubicThetaPrimeCubeDilationSection hp G))]
  rw [←cubicThetaPrimeCubeTrace_pairing hp (cubicThetaPrimeCubeDilationSection hp G) F hcG hF]
  rfl

theorem cubicThetaPrimeCubeRootTrace_finite {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaSmoothTests) :
    inner ℂ (cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothRestriction hp F))
      (cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothDilation hp G))=
      ((cubicThetaPrimeCubeRootHeckeSubgroup hp).index:ℝ) •
        inner ℂ (cubicThetaGlobalMassClosure F)
          (cubicThetaPrimeCubeHeckeMass hp (cubicThetaGlobalMassClosure G)) := by
  rw [cubicThetaPrimeCubeRootFinite_pairing]
  change (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,
    star (F.val.val x)*(cubicThetaPrimeCubeDilationSection hp G.val).val x ∂cubicThetaPointMeasure)=_
  rw [cubicThetaPrimeCubeRootTrace_integral hp F.val G.val
    (cubicThetaPrimeCubeFinite_mass_domain (cubicThetaSmoothToFiniteEnergy F))
    (cubicThetaPrimeCubeFinite_mass_domain (cubicThetaSmoothToFiniteEnergy G))]
  congr 1
  change _=inner ℂ (cubicThetaFiniteMassClosure (cubicThetaSmoothToFiniteEnergy F))
    (cubicThetaPrimeCubeHeckeMass hp (cubicThetaFiniteMassClosure (cubicThetaSmoothToFiniteEnergy G)))
  rw [cubicThetaPrimeCubeHeckeMass_finite]
  change _=inner ℂ (cubicThetaFiniteEnergyValue (cubicThetaSmoothToFiniteEnergy F))
    (cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeHeckeFinite hp (cubicThetaSmoothToFiniteEnergy G)))
  rw [cubicThetaFiniteEnergyValue_pairing]
  apply integral_congr_ae
  filter_upwards with x
  exact (RCLike.inner_apply' _ _).symm

end CubicFirstMoment

end

end OAI
