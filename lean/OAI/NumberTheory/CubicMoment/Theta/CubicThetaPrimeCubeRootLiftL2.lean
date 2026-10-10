import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootAutomorphicL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootDomainMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeLiftL2

namespace OAI

/-! Normalized isometric lifting from the original automorphic Hilbert
space to the actual root cover. -/
noncomputable section
namespace CubicFirstMoment

local instance cubeRootLift_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaPrimeCubeRootSmoothRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeCubeRootFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeRootSectionRestrict F.val,
    cubicThetaPrimeCubeRootDomain_global_memLp hp F.val (cubicThetaSectionRepresentative_memLp F)⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeCubeRootSmoothRestriction_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothRestriction hp F)‖^2=
      ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)*‖cubicThetaGlobalMassClosure F‖^2 :=
  by
    change ‖cubicThetaPrimeCubeRootFiniteValue hp (cubicThetaPrimeCubeRootSmoothRestriction hp F)‖^2=_
    rw [cubicThetaPrimeCubeRootSectionL2_norm_sq]
    change (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,‖F.val.val x‖^2 ∂cubicThetaPointMeasure)=_
    rw [cubicThetaPrimeCubeRootDomain_global_mass]
    change ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)*
      (∫ q, (cubicThetaSectionNorm F.val q)^2 ∂cubicThetaQuotientMeasure)=
      ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)*
        ‖cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)‖^2
    rw [cubicThetaGlobalInclusion_test_norm_sq]

lemma cubicThetaPrimeCubeRootCoverDegree_pos {p : Eisenstein} (hp : primaryPrime p) :
    0<((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)

def cubicThetaPrimeCubeRootNormalizedRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  ((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ) •
    ((cubicThetaPrimeCubeRootFiniteEmbedding hp).comp (cubicThetaPrimeCubeRootSmoothRestriction hp))

lemma cubicThetaPrimeCubeRootNormalizedRestriction_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeCubeRootNormalizedRestriction hp F‖=‖cubicThetaGlobalMassClosure F‖ := by
  let d : ℝ := (cubicThetaPrimeCubeRootCoverGroup hp).index
  have hd : 0<d := cubicThetaPrimeCubeRootCoverDegree_pos hp
  have hc : ‖((Real.sqrt d)⁻¹:ℂ)‖^2*d=1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,inv_pow,sq_abs,Real.sq_sqrt hd.le,
      inv_mul_cancel₀ hd.ne']
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  change ‖((Real.sqrt d)⁻¹:ℂ) •
    cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothRestriction hp F)‖^2=_
  rw [norm_smul,mul_pow,cubicThetaPrimeCubeRootSmoothRestriction_norm_sq]
  change ‖((Real.sqrt d)⁻¹:ℂ)‖^2*(d*‖cubicThetaGlobalMassClosure F‖^2)=_
  rw [←mul_assoc,hc,one_mul]

def cubicThetaPrimeCubeRootLiftL2 {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaAutomorphicL2 →ₗᵢ[ℂ] cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  (cubicThetaPrimeCubeRootNormalizedRestriction hp).extendOfIsometry
    cubicThetaGlobalMassClosure_dense (cubicThetaPrimeCubeRootNormalizedRestriction_norm hp)

lemma cubicThetaPrimeCubeRootLiftL2_smooth {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaGlobalMassClosure F)=
      cubicThetaPrimeCubeRootNormalizedRestriction hp F :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
