import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootBruhatPhase
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootWeylL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionSmooth

namespace OAI

/-! The actual twice-cubically-dilated global branch and its invariance
under all cubic-scale translations. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootWeyl_global_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (z : CubicThetaPoint) :
    (cubicThetaPrimeCubeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val z=
      (cubicThetaInversionSection F).val
        (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • z)) := by
  change F.val (cubicThetaPrimeCubeRootWeylElement hp • z)=_
  rw [cubicThetaPrimeCubeRootWeylElement,cubicThetaPrimeCubeAtkinMatrix,mul_smul,mul_smul]
  rfl

lemma cubicThetaPrimeCubeRootWeyl_global_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : CubicThetaSection) :
    cubicThetaPrimeCubeRootSectionTranslate hp x
      (cubicThetaPrimeCubeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F))=
        cubicThetaPrimeCubeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F) := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)
  let t := cubicThetaPrincipalTranslation x
  let g : cubicThetaPrimeIwahori (p^3) := ⟨t,by change p^3∣0; exact dvd_zero (p^3)⟩
  have h1 : D*cubicThetaPrimeCubeRootElement hp x=cubicThetaPrincipalComplex t*D := by
    dsimp only [D,t,cubicThetaPrimeCubeRootElement]
    group
  have h2 : D*cubicThetaPrincipalComplex t=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g)*D :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeCube_primary hp) g
  have h3 : D*(D*cubicThetaPrimeCubeRootElement hp x)=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g)*(D*D) := by
    rw [h1,←mul_assoc,h2,mul_assoc]
  have hk : cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g)=1 := by
    rw [cubicThetaKubotaValue_eq_symbol]
    simp [g,t,cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,
      cubicThetaPrincipalTranslation,cubicSymbol_one_lower]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change (cubicThetaPrimeCubeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val
    (cubicThetaPrimeCubeRootElement hp x • y)=_
  rw [cubicThetaPrimeCubeRootWeyl_global_zero,cubicThetaPrimeCubeRootWeyl_global_zero]
  change (cubicThetaInversionSection F).val (D • (D • (cubicThetaPrimeCubeRootElement hp x • y)))=
    (cubicThetaInversionSection F).val (D • (D • y))
  rw [←mul_smul,←mul_smul,mul_assoc,h3,mul_smul,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g • (D • (D • y)))=_
  rw [(cubicThetaInversionSection F).property,hk,one_mul]


lemma cubicThetaPrimeCubeRootWeyl_finite_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaSmoothTests) :
    cubicThetaPrimeCubeRootFiniteTranslate hp x
      (cubicThetaPrimeCubeRootFiniteWeyl hp (cubicThetaPrimeCubeRootSmoothRestriction hp F))=
        cubicThetaPrimeCubeRootFiniteWeyl hp (cubicThetaPrimeCubeRootSmoothRestriction hp F) := by
  apply Subtype.ext
  exact cubicThetaPrimeCubeRootWeyl_global_translate hp x F.val

theorem cubicThetaPrimeCubeRootWeyl_lift_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeCubeRootTranslateL2 hp x
      (cubicThetaPrimeCubeRootWeylL2 hp (cubicThetaPrimeCubeRootLiftL2 hp u))=
        cubicThetaPrimeCubeRootWeylL2 hp (cubicThetaPrimeCubeRootLiftL2 hp u) := by
  refine cubicThetaGlobalMassClosure_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeCubeRootTranslateL2 hp x).continuous.comp
      ((cubicThetaPrimeCubeRootWeylL2 hp).continuous.comp (cubicThetaPrimeCubeRootLiftL2 hp).continuous))
      ((cubicThetaPrimeCubeRootWeylL2 hp).continuous.comp (cubicThetaPrimeCubeRootLiftL2 hp).continuous)) ?_
  intro F
  simp only [cubicThetaPrimeCubeRootLiftL2_smooth,cubicThetaPrimeCubeRootNormalizedRestriction,
    LinearMap.smul_apply,LinearMap.comp_apply,map_smul,cubicThetaPrimeCubeRootWeylL2_finite,
    cubicThetaPrimeCubeRootTranslateL2_finite,cubicThetaPrimeCubeRootWeyl_finite_translate]

end CubicFirstMoment

end

end OAI
