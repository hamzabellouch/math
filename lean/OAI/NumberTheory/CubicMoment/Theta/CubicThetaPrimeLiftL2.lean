import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeAutomorphicL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRestrictionL2

namespace OAI

/-! Normalized lifting from the original automorphic L2 closure to the
actual finite prime cover. The normalization is the square root of its degree. -/
noncomputable section
open Topology
namespace CubicFirstMoment

local instance primeLift_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaGlobalMassClosure : cubicThetaSmoothTests →ₗ[ℂ] cubicThetaAutomorphicL2 :=
  cubicThetaGlobalMass.codRestrict cubicThetaAutomorphicL2
    (fun F => Submodule.le_topologicalClosure _ ⟨F,rfl⟩)

lemma cubicThetaGlobalMassClosure_dense : DenseRange cubicThetaGlobalMassClosure := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' Set.range cubicThetaGlobalMassClosure=Set.range cubicThetaGlobalMass := by
    ext y
    constructor
    · rintro ⟨v,⟨F,rfl⟩,rfl⟩
      exact ⟨F,rfl⟩
    · rintro ⟨F,rfl⟩
      exact ⟨cubicThetaGlobalMassClosure F,⟨F,rfl⟩,rfl⟩
  rw [he]
  exact u.property

def cubicThetaPrimeSmoothRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeSectionRestrict hp F.val,
    cubicThetaPrimeSectionRestrict_memLp hp F.val (cubicThetaSectionRepresentative_memLp F)⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeSmoothRestriction_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeFiniteEmbedding hp (cubicThetaPrimeSmoothRestriction hp F)‖^2=
      ((cubicThetaPrimeCoverGroup hp).index:ℝ)*‖cubicThetaGlobalMassClosure F‖^2 :=
  cubicThetaPrimeSectionRestrict_L2_norm_sq hp F.val (cubicThetaSectionRepresentative_memLp F)

lemma cubicThetaPrimeCoverDegree_pos {p : Eisenstein} (hp : primaryPrime p) :
    0<((cubicThetaPrimeCoverGroup hp).index:ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)

def cubicThetaPrimeNormalizedRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeAutomorphicL2 hp :=
  ((Real.sqrt ((cubicThetaPrimeCoverGroup hp).index:ℝ))⁻¹:ℂ) •
    ((cubicThetaPrimeFiniteEmbedding hp).comp (cubicThetaPrimeSmoothRestriction hp))

lemma cubicThetaPrimeNormalizedRestriction_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeNormalizedRestriction hp F‖=‖cubicThetaGlobalMassClosure F‖ := by
  let d : ℝ := (cubicThetaPrimeCoverGroup hp).index
  have hd : 0<d := cubicThetaPrimeCoverDegree_pos hp
  have hc : ‖((Real.sqrt d)⁻¹:ℂ)‖^2*d=1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,inv_pow,sq_abs,Real.sq_sqrt hd.le,
      inv_mul_cancel₀ hd.ne']
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  change ‖((Real.sqrt d)⁻¹:ℂ) •
    cubicThetaPrimeFiniteEmbedding hp (cubicThetaPrimeSmoothRestriction hp F)‖^2=_
  rw [norm_smul,mul_pow,cubicThetaPrimeSmoothRestriction_norm_sq]
  change ‖((Real.sqrt d)⁻¹:ℂ)‖^2*(d*‖cubicThetaGlobalMassClosure F‖^2)=_
  rw [←mul_assoc,hc,one_mul]

def cubicThetaPrimeLiftL2 {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaAutomorphicL2 →ₗᵢ[ℂ] cubicThetaPrimeAutomorphicL2 hp :=
  (cubicThetaPrimeNormalizedRestriction hp).extendOfIsometry
    cubicThetaGlobalMassClosure_dense (cubicThetaPrimeNormalizedRestriction_norm hp)

lemma cubicThetaPrimeLiftL2_smooth {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    cubicThetaPrimeLiftL2 hp (cubicThetaGlobalMassClosure F)=
      cubicThetaPrimeNormalizedRestriction hp F :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
