import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeOppositeConjugation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDilationCoordinates

namespace OAI

/-! The complementary chart contributes the missing nonunit translations
in the lowest branch, with complete cancellation of its two multipliers. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeOpposite_section {p : Eisenstein} (hp : primaryPrime p)
    (m : Eisenstein) (F : CubicThetaSection) (x : CubicThetaPoint) :
    star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        ((cubicThetaPrimeCubeWeyl hp*cubicThetaPrincipalTranslation m) • x))=
      F.val ((cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ •
        (cubicThetaPrincipalTranslation m • x)) := by
  have hu : star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
      cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  rw [mul_smul]
  change star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
    F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      (cubicThetaPrincipalComplex (cubicThetaPrimeCubeWeyl hp) •
        (cubicThetaPrincipalTranslation m • x)))=_
  rw [←mul_smul,cubicThetaPrimeCubeOpposite_intertwines,mul_smul]
  change star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
    F.val (cubicThetaPrimeCubeOpposite hp •
      ((cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ •
        (cubicThetaPrincipalTranslation m • x)))=_
  rw [F.property,cubicThetaPrimeCubeOpposite_kubota,←mul_assoc,hu,one_mul]

lemma cubicThetaPrimeCubeInverse_branchPoint {p : Eisenstein} (hp : primaryPrime p)
    (m : Eisenstein) (x : CubicThetaPoint) :
    (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ •
      (cubicThetaPrincipalTranslation m • x)=cubicThetaPrimeCubeBranchPoint hp 0 m x := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hn : ‖(p:ℂ)‖≠0 := norm_ne_zero_iff.mpr hpC
  have hp3norm : ‖((p^3:Eisenstein):ℂ)‖=‖(p:ℂ)‖^3 := by
    rw [show ((p^3:Eisenstein):ℂ)=(p:ℂ)^3 from
      map_pow (eisensteinRing.subtype : Eisenstein →+* ℂ) p 3,norm_pow]
  have he : D • cubicThetaPrimeCubeBranchPoint hp 0 m x=cubicThetaPrincipalTranslation m • x := by
    apply Subtype.ext
    change cubicThetaMobius D (cubicThetaPrimeCubeBranchPoint hp 0 m x).val=
      cubicThetaMobius (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation m)) x.val
    rw [cubicThetaPrincipalTranslation_complex,cubicThetaMobius_translation]
    change cubicThetaMobius (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)) _=_
    rw [cubicThetaMobius_primeDilation]
    apply Prod.ext
    · change ((p^3:Eisenstein):ℂ)*
        ((p:ℂ)^0/(p:ℂ)^(3-0)*x.val.1+((3*m:Eisenstein):ℂ)/(p:ℂ)^(3-0))=
          x.val.1+((3*m:Eisenstein):ℂ)
      push_cast
      field_simp
    · change ‖((p^3:Eisenstein):ℂ)‖*
        ((‖(p:ℂ)‖^0/‖(p:ℂ)‖^(3-0))*x.val.2)=x.val.2
      rw [hp3norm]
      simp [hn]
  have hi := congrArg (fun y : CubicThetaPoint => D⁻¹ • y) he
  simpa only [smul_smul,inv_mul_cancel,one_smul] using hi.symm

theorem cubicThetaPrimeCubeUpperBranch {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) (r : cubicThetaPrimeCubeUpperParameter p) :
    star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        (cubicThetaPrimeCubeUpperRepresentative hp r • x))=
      F.val (cubicThetaPrimeCubeBranchPoint hp 0 (residueRepresentative (p^3) r.val) x) := by
  rw [cubicThetaPrimeCubeUpperRepresentative,cubicThetaPrimeCubeOpposite_section,
    cubicThetaPrimeCubeInverse_branchPoint]

end CubicFirstMoment

end

end OAI
