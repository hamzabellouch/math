import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootHeckeIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootLiftL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFiniteEnergy

namespace OAI

/-! The once-cubic dilation is an actual square-integrable section on
K3. Its finite-domain norm has the original global covering degree. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootHeckeRestriction {p : Eisenstein} (_hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) : cubicThetaPrimeCubeRootSections p :=
  ⟨F.val,by
    intro g x
    exact F.property (cubicThetaPrimeCubeRootIwahori g) x⟩

lemma cubicThetaPrimeCubeRootDilation_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    IntegrableOn (fun x => ‖(cubicThetaPrimeCubeDilationSection hp F).val x‖^2)
      (cubicThetaPrimeCubeRootCoverDomain hp) cubicThetaPointMeasure :=
  cubicThetaPrimeCubeRootHecke_integrable hp (cubicThetaPrimeCubeDilation_integrable hp F hF)
    (cubicThetaPrimeCubeSection_norm_invariant p (cubicThetaPrimeCubeDilationSection hp F))

theorem cubicThetaPrimeCubeRootDilation_mass {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,
      ‖(cubicThetaPrimeCubeDilationSection hp F).val x‖^2 ∂cubicThetaPointMeasure)=
      ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)*
        ∫ x in cubicThetaFundamentalDomain,‖F.val x‖^2 ∂cubicThetaPointMeasure := by
  rw [cubicThetaPrimeCubeRootHecke_integral hp
    (cubicThetaPrimeCubeDilation_integrable hp F hF)
    (cubicThetaPrimeCubeSection_norm_invariant p (cubicThetaPrimeCubeDilationSection hp F)),
    smul_eq_mul,cubicThetaPrimeCubeDilation_integral_norm hp F hF,←mul_assoc,←Nat.cast_mul,
    cubicThetaPrimeCubeRootHecke_index hp]

def cubicThetaPrimeCubeRootSmoothDilation {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeCubeRootFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeCubeRootHeckeRestriction hp (cubicThetaPrimeCubeDilationSection hp F.val),by
    apply (memLp_two_iff_integrable_sq_norm
      (cubicThetaPrimeCubeRootHeckeRestriction hp
        (cubicThetaPrimeCubeDilationSection hp F.val)).val.continuous.aestronglyMeasurable).mpr
    exact cubicThetaPrimeCubeRootDilation_integrable hp F.val
      (cubicThetaPrimeCubeFinite_mass_domain (cubicThetaSmoothToFiniteEnergy F))⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeCubeRootSmoothDilation_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothDilation hp F)‖^2=
      ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)*‖cubicThetaGlobalMassClosure F‖^2 := by
  change ‖cubicThetaPrimeCubeRootFiniteValue hp (cubicThetaPrimeCubeRootSmoothDilation hp F)‖^2=_
  rw [cubicThetaPrimeCubeRootSectionL2_norm_sq]
  change (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,
    ‖(cubicThetaPrimeCubeDilationSection hp F.val).val x‖^2 ∂cubicThetaPointMeasure)=_
  rw [cubicThetaPrimeCubeRootDilation_mass hp F.val
    (cubicThetaPrimeCubeFinite_mass_domain (cubicThetaSmoothToFiniteEnergy F))]
  congr 1
  exact (cubicThetaFiniteEnergyValue_domain_norm_sq (cubicThetaSmoothToFiniteEnergy F)).symm

end CubicFirstMoment

end

end OAI
