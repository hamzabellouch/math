import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootDilation

namespace OAI

/-! Normalized isometric cubic dilation of the actual global mass space
into the common arithmetic root cover. -/
noncomputable section
namespace CubicFirstMoment

local instance cubeRootDilation_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaPrimeCubeRootNormalizedDilation {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  ((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ) •
    ((cubicThetaPrimeCubeRootFiniteEmbedding hp).comp (cubicThetaPrimeCubeRootSmoothDilation hp))

lemma cubicThetaPrimeCubeRootNormalizedDilation_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeCubeRootNormalizedDilation hp F‖=‖cubicThetaGlobalMassClosure F‖ := by
  let d : ℝ := (cubicThetaPrimeCubeRootCoverGroup hp).index
  have hd : 0<d := cubicThetaPrimeCubeRootCoverDegree_pos hp
  have hc : ‖((Real.sqrt d)⁻¹:ℂ)‖^2*d=1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,inv_pow,sq_abs,Real.sq_sqrt hd.le,
      inv_mul_cancel₀ hd.ne']
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  change ‖((Real.sqrt d)⁻¹:ℂ) •
    cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothDilation hp F)‖^2=_
  rw [norm_smul,mul_pow,cubicThetaPrimeCubeRootSmoothDilation_norm_sq]
  change ‖((Real.sqrt d)⁻¹:ℂ)‖^2*(d*‖cubicThetaGlobalMassClosure F‖^2)=_
  rw [←mul_assoc,hc,one_mul]

def cubicThetaPrimeCubeRootDilationL2 {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaAutomorphicL2 →ₗᵢ[ℂ] cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  (cubicThetaPrimeCubeRootNormalizedDilation hp).extendOfIsometry
    cubicThetaGlobalMassClosure_dense (cubicThetaPrimeCubeRootNormalizedDilation_norm hp)

lemma cubicThetaPrimeCubeRootDilationL2_smooth {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    cubicThetaPrimeCubeRootDilationL2 hp (cubicThetaGlobalMassClosure F)=
      cubicThetaPrimeCubeRootNormalizedDilation hp F :=
  LinearMap.extendOfIsometry_eq _ _ _ F


end CubicFirstMoment

end

end OAI
