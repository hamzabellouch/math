import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeReciprocalGeometry

namespace OAI

/-! The reciprocal coset permutation identifies the actual adjoint
correspondence with the original cubed-prime operator. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCube_inverse_section {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (y : CubicThetaPoint) :
    F.val ((cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ • y)=
      star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
        F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
          (cubicThetaPrimeCubeWeyl hp • y)) := by
  have hu : star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
      cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  symm
  change star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
    F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      (cubicThetaPrincipalComplex (cubicThetaPrimeCubeWeyl hp) • y))=_
  rw [←mul_smul,cubicThetaPrimeCubeOpposite_intertwines,mul_smul]
  change star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
    F.val (cubicThetaPrimeCubeOpposite hp •
      ((cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ • y))=_
  rw [F.property,cubicThetaPrimeCubeOpposite_kubota,←mul_assoc,hu,one_mul]

lemma cubicThetaPrimeCube_reciprocal_term {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    star (cubicThetaKubotaValue g)*F.val (cubicThetaFullInversion •
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        (g • (cubicThetaFullInversion • x))))=
      star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
        cubicThetaPrimeCubeTraceTerm p (cubicThetaPrimeCubeDilationSection hp F)
          (cubicThetaPrincipalConjugate (cubicThetaPrimeCubeReciprocalNormalizer hp) g)
          (cubicThetaPrimeCubeWeyl hp • x) := by
  have hg : cubicThetaPrimeCubeWeyl hp*cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g=
      cubicThetaPrincipalConjugate (cubicThetaPrimeCubeReciprocalNormalizer hp) g*cubicThetaPrimeCubeWeyl hp := by
    rw [cubicThetaPrimeCubeReciprocalNormalizer_conjugate]
    group
  have hx : cubicThetaPrimeCubeWeyl hp •
      (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g • x)=
      cubicThetaPrincipalConjugate (cubicThetaPrimeCubeReciprocalNormalizer hp) g •
        (cubicThetaPrimeCubeWeyl hp • x) := by
    rw [←mul_smul,hg,mul_smul]
  rw [cubicThetaPrimeCube_reciprocal_point hp,cubicThetaPrimeCube_inverse_section hp,hx]
  unfold cubicThetaPrimeCubeTraceTerm
  rw [cubicThetaPrimeCubeReciprocalNormalizer_character]
  change star (cubicThetaKubotaValue g) *
      (star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)) *
        F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
          (cubicThetaPrincipalConjugate (cubicThetaPrimeCubeReciprocalNormalizer hp) g •
            (cubicThetaPrimeCubeWeyl hp • x)))) =
    star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)) *
      (star (cubicThetaKubotaValue g) *
        F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
          (cubicThetaPrincipalConjugate (cubicThetaPrimeCubeReciprocalNormalizer hp) g •
            (cubicThetaPrimeCubeWeyl hp • x))))
  ring

theorem cubicThetaPrimeCubeHecke_inversion_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) :
    cubicThetaInversionSection (cubicThetaPrimeCubeHecke hp (cubicThetaInversionSection F))=
      cubicThetaPrimeCubeHecke hp F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (cubicThetaPrimeCubeHecke hp (cubicThetaInversionSection F)).val
    (cubicThetaFullInversion • x)=(cubicThetaPrimeCubeHecke hp F).val x
  rw [cubicThetaPrimeCubeHecke_apply]
  change (∑' t : cubicThetaPrimeCubeTransversal p,star (cubicThetaKubotaValue t.val)*
    F.val (cubicThetaFullInversion • (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      (t.val • (cubicThetaFullInversion • x)))))=_
  simp_rw [cubicThetaPrimeCube_reciprocal_term hp]
  rw [tsum_mul_left,cubicThetaPrimeCubeTrace_normalizer hp _ (cubicThetaPrimeCubeReciprocalNormalizer_lower hp)]
  change star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
    (cubicThetaPrimeCubeHecke hp F).val (cubicThetaPrimeCubeWeyl hp • x)=_
  rw [(cubicThetaPrimeCubeHecke hp F).property,←mul_assoc]
  have hu : star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
      cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  rw [hu,one_mul]

end CubicFirstMoment

end

end OAI
