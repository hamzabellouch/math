import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeEnergyRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalLocalRellich

namespace OAI

/-! The degree-normalized restriction extends isometrically from actual
compact smooth sections to the completed original energy space. -/
noncomputable section
namespace CubicFirstMoment

local instance primeLiftEnergy_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaPrimeNormalizedEnergyRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeEnergySpace hp :=
  ((Real.sqrt ((cubicThetaPrimeCoverGroup hp).index:ℝ))⁻¹:ℂ) •
    ((cubicThetaPrimeEnergyTest hp).comp (cubicThetaPrimeSmoothEnergyRestriction hp))

lemma cubicThetaPrimeNormalizedEnergyRestriction_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeNormalizedEnergyRestriction hp F‖=‖cubicThetaGlobalEnergyTestLinear F‖ := by
  let d : ℝ := (cubicThetaPrimeCoverGroup hp).index
  have hd : 0<d := cubicThetaPrimeCoverDegree_pos hp
  have hc : ‖((Real.sqrt d)⁻¹:ℂ)‖^2*d=1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,inv_pow,sq_abs,Real.sq_sqrt hd.le,
      inv_mul_cancel₀ hd.ne']
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  change ‖((Real.sqrt d)⁻¹:ℂ) •
    cubicThetaPrimeEnergyTest hp (cubicThetaPrimeSmoothEnergyRestriction hp F)‖^2=_
  rw [norm_smul,mul_pow,cubicThetaPrimeSmoothEnergyRestriction_norm_sq]
  change ‖((Real.sqrt d)⁻¹:ℂ)‖^2*(d*‖cubicThetaGlobalEnergyTestLinear F‖^2)=_
  rw [←mul_assoc,hc,one_mul]

def cubicThetaPrimeLiftEnergy {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaGlobalEnergySpace →ₗᵢ[ℂ] cubicThetaPrimeEnergySpace hp :=
  (cubicThetaPrimeNormalizedEnergyRestriction hp).extendOfIsometry
    cubicThetaGlobalEnergyTestLinear_dense (cubicThetaPrimeNormalizedEnergyRestriction_norm hp)

lemma cubicThetaPrimeLiftEnergy_smooth {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    cubicThetaPrimeLiftEnergy hp (cubicThetaGlobalEnergyTest F)=
      cubicThetaPrimeNormalizedEnergyRestriction hp F :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
