import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeNormalizerCosets
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeCompletedAdjoint

namespace OAI

/-! Reciprocal geometry and multiplier identities for the literal
cubed-prime correspondence. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeReciprocalNormalizer_conjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrincipalGroup) :
    cubicThetaPrincipalConjugate (cubicThetaPrimeCubeReciprocalNormalizer hp) g=
      cubicThetaPrimeCubeWeyl hp*cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g*
        (cubicThetaPrimeCubeWeyl hp)⁻¹ := by
  apply Subtype.ext
  change (((cubicThetaPrimeCubeWeyl hp).val*cubicThetaFullInversion)⁻¹)⁻¹*g.val*
    ((cubicThetaPrimeCubeWeyl hp).val*cubicThetaFullInversion)⁻¹=
    (cubicThetaPrimeCubeWeyl hp).val*
      ((cubicThetaFullInversion⁻¹)⁻¹*g.val*cubicThetaFullInversion⁻¹)*
      (cubicThetaPrimeCubeWeyl hp).val⁻¹
  group

lemma cubicThetaPrimeCubeReciprocalNormalizer_character {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue (cubicThetaPrincipalConjugate (cubicThetaPrimeCubeReciprocalNormalizer hp) g)=
      cubicThetaKubotaValue g := by
  rw [cubicThetaPrimeCubeReciprocalNormalizer_conjugate,cubicThetaKubotaValue_mul,
    cubicThetaKubotaValue_mul,cubicThetaInversionConjugate_character]
  have he : cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)*
      cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)⁻¹=1 := by
    change cubicThetaKubotaCharacter (cubicThetaPrimeCubeWeyl hp)*
      cubicThetaKubotaCharacter ((cubicThetaPrimeCubeWeyl hp)⁻¹)=1
    rw [←map_mul,mul_inv_cancel,map_one]
  calc
    _ = cubicThetaKubotaValue g*(cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)*
      cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)⁻¹) := by ring
    _ = _ := by rw [he,mul_one]

lemma cubicThetaPrimeCube_inversion_dilation {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    cubicThetaFullInversion • (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)=
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ • (cubicThetaFullInversion • x) := by
  have he : cubicThetaFullComplex cubicThetaFullInversion*
      cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)=
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹*
        cubicThetaFullComplex cubicThetaFullInversion := by
    rw [cubicThetaFullInversion_complex]
    apply Subtype.ext
    change (cubicThetaInversionMatrix 1 one_ne_zero : Matrix (Fin 2) (Fin 2) ℂ)*
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) : Matrix (Fin 2) (Fin 2) ℂ)=
      Matrix.adjugate (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) : Matrix (Fin 2) (Fin 2) ℂ)*
        (cubicThetaInversionMatrix 1 one_ne_zero : Matrix (Fin 2) (Fin 2) ℂ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubicThetaInversionMatrix,cubicThetaPrimeDilation,Matrix.adjugate_fin_two,
        Matrix.mul_apply,Fin.sum_univ_two]

  change cubicThetaFullComplex cubicThetaFullInversion •
    (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)=_
  rw [←mul_smul,he,mul_smul]
  rfl

lemma cubicThetaPrimeCube_reciprocal_point {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    cubicThetaFullInversion • (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      (g • (cubicThetaFullInversion • x)))=
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ •
        (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g • x) := by
  rw [cubicThetaPrimeCube_inversion_dilation hp,cubicThetaInversion_intertwine,
    cubicThetaFullInversion_involutive]

end CubicFirstMoment

end

end OAI
