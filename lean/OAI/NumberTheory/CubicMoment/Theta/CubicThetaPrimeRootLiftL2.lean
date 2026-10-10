import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootAutomorphicL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootRestrictionL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeLiftL2

namespace OAI

/-! Normalized isometric lifting from the original automorphic Hilbert
space to the actual root cover. -/
noncomputable section
namespace CubicFirstMoment

local instance rootLift_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaPrimeRootSmoothRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeRootFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeRootSectionRestrict F.val,
    cubicThetaPrimeRootSectionRestrict_memLp hp F.val (cubicThetaSectionRepresentative_memLp F)⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeRootSmoothRestriction_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootSmoothRestriction hp F)‖^2=
      ((cubicThetaPrimeRootCoverGroup hp).index:ℝ)*‖cubicThetaGlobalMassClosure F‖^2 :=
  cubicThetaPrimeRootSectionRestrict_L2_norm_sq hp F.val (cubicThetaSectionRepresentative_memLp F)

lemma cubicThetaPrimeRootCoverDegree_pos {p : Eisenstein} (hp : primaryPrime p) :
    0<((cubicThetaPrimeRootCoverGroup hp).index:ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)

def cubicThetaPrimeRootNormalizedRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeRootAutomorphicL2 hp :=
  ((Real.sqrt ((cubicThetaPrimeRootCoverGroup hp).index:ℝ))⁻¹:ℂ) •
    ((cubicThetaPrimeRootFiniteEmbedding hp).comp (cubicThetaPrimeRootSmoothRestriction hp))

lemma cubicThetaPrimeRootNormalizedRestriction_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeRootNormalizedRestriction hp F‖=‖cubicThetaGlobalMassClosure F‖ := by
  let d : ℝ := (cubicThetaPrimeRootCoverGroup hp).index
  have hd : 0<d := cubicThetaPrimeRootCoverDegree_pos hp
  have hc : ‖((Real.sqrt d)⁻¹:ℂ)‖^2*d=1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,inv_pow,sq_abs,Real.sq_sqrt hd.le,
      inv_mul_cancel₀ hd.ne']
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  change ‖((Real.sqrt d)⁻¹:ℂ) •
    cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootSmoothRestriction hp F)‖^2=_
  rw [norm_smul,mul_pow,cubicThetaPrimeRootSmoothRestriction_norm_sq]
  change ‖((Real.sqrt d)⁻¹:ℂ)‖^2*(d*‖cubicThetaGlobalMassClosure F‖^2)=_
  rw [←mul_assoc,hc,one_mul]

def cubicThetaPrimeRootLiftL2 {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaAutomorphicL2 →ₗᵢ[ℂ] cubicThetaPrimeRootAutomorphicL2 hp :=
  (cubicThetaPrimeRootNormalizedRestriction hp).extendOfIsometry
    cubicThetaGlobalMassClosure_dense (cubicThetaPrimeRootNormalizedRestriction_norm hp)

lemma cubicThetaPrimeRootLiftL2_smooth {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    cubicThetaPrimeRootLiftL2 hp (cubicThetaGlobalMassClosure F)=
      cubicThetaPrimeRootNormalizedRestriction hp F :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
