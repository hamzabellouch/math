import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylGauss

namespace OAI

/-! The retained twice-dilated branch is fixed by the root group. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeyl_global_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : CubicThetaSection) :
    cubicThetaPrimeRootSectionTranslate hp x
      (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F))=
        cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F) := by
  let D := cubicThetaPrimeDilation hp.2.ne_zero
  let t := cubicThetaPrincipalTranslation x
  let g : cubicThetaPrimeIwahori p := ⟨t,by change p∣0; exact dvd_zero p⟩
  have h1 : D*cubicThetaPrimeRootElement hp x=cubicThetaPrincipalComplex t*D := by
    dsimp only [D,t,cubicThetaPrimeRootElement]
    group
  have h2 : D*cubicThetaPrincipalComplex t=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 g)*D :=
    cubicThetaPrimeDilation_intertwines hp.1 g
  have h3 : D*(D*cubicThetaPrimeRootElement hp x)=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 g)*(D*D) := by
    rw [h1,←mul_assoc,h2,mul_assoc]
  have hk : cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 g)=1 := by
    rw [cubicThetaKubotaValue_eq_symbol]
    simp [g,t,cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,
      cubicThetaPrincipalTranslation,cubicSymbol_one_lower]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val
    (cubicThetaPrimeRootElement hp x • y)=_
  rw [cubicThetaPrimeRootWeyl_global_zero,cubicThetaPrimeRootWeyl_global_zero]
  change (cubicThetaInversionSection F).val (D • (D • (cubicThetaPrimeRootElement hp x • y)))=
    (cubicThetaInversionSection F).val (D • (D • y))
  rw [←mul_smul,←mul_smul,mul_assoc,h3,mul_smul,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeConjugate hp.1 g • (D • (D • y)))=_
  rw [(cubicThetaInversionSection F).property,hk,one_mul]

lemma cubicThetaPrimeRootWeyl_finite_translate {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (F : cubicThetaSmoothTests) :
    cubicThetaPrimeRootFiniteResidue hp r
      (cubicThetaPrimeRootFiniteWeyl hp (cubicThetaPrimeRootSmoothRestriction hp F))=
        cubicThetaPrimeRootFiniteWeyl hp (cubicThetaPrimeRootSmoothRestriction hp F) := by
  apply Subtype.ext
  exact cubicThetaPrimeRootWeyl_global_translate hp (residueRepresentative p r) F.val

theorem cubicThetaPrimeRootWeyl_lift_translate {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeRootResidueL2 hp r
      (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u))=
        cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u) := by
  refine cubicThetaGlobalMassClosure_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeRootResidueL2 hp r).continuous.comp
      ((cubicThetaPrimeRootWeylL2 hp).continuous.comp (cubicThetaPrimeRootLiftL2 hp).continuous))
      ((cubicThetaPrimeRootWeylL2 hp).continuous.comp (cubicThetaPrimeRootLiftL2 hp).continuous)) ?_
  intro F
  simp only [cubicThetaPrimeRootLiftL2_smooth,cubicThetaPrimeRootNormalizedRestriction,
    LinearMap.smul_apply,LinearMap.comp_apply,map_smul,cubicThetaPrimeRootWeylL2_finite,
    cubicThetaPrimeRootResidueL2_finite,cubicThetaPrimeRootWeyl_finite_translate]

lemma cubicThetaPrimeRootWeyl_finite_fourier {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    cubicThetaPrimeRootFiniteFourier hp 0
      (cubicThetaPrimeRootFiniteWeyl hp (cubicThetaPrimeRootSmoothRestriction hp F))=
        cubicThetaPrimeRootFiniteWeyl hp (cubicThetaPrimeRootSmoothRestriction hp F) := by
  apply Subtype.ext
  rw [cubicThetaPrimeRootFiniteFourier_val,cubicThetaPrimeRootFourierProjection_zero]
  apply cubicThetaPrimeRootAverage_fixed
  intro r
  exact cubicThetaPrimeRootWeyl_global_translate hp (residueRepresentative p r) F.val

theorem cubicThetaPrimeRootWeyl_lift_fourier {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeRootFourierL2 hp 0
      (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u))=
        cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u) := by
  refine cubicThetaGlobalMassClosure_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeRootFourierL2 hp 0).continuous.comp
      ((cubicThetaPrimeRootWeylL2 hp).continuous.comp (cubicThetaPrimeRootLiftL2 hp).continuous))
      ((cubicThetaPrimeRootWeylL2 hp).continuous.comp (cubicThetaPrimeRootLiftL2 hp).continuous)) ?_
  intro F
  simp only [cubicThetaPrimeRootLiftL2_smooth,cubicThetaPrimeRootNormalizedRestriction,
    LinearMap.smul_apply,LinearMap.comp_apply,map_smul,cubicThetaPrimeRootWeylL2_finite,
    cubicThetaPrimeRootFourierL2_finite,cubicThetaPrimeRootWeyl_finite_fourier]

theorem cubicThetaPrimeRootWeyl_lift_fourier_nonzero {p : Eisenstein} (hp : primaryPrime p)
    (j : Residues p) (hj : j≠0) (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeRootFourierL2 hp j
      (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u))=0 := by
  have he := cubicThetaPrimeRootFourierL2_product hp j 0
    (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u))
  rw [cubicThetaPrimeRootWeyl_lift_fourier,ite_eq_right hj] at he
  exact he

end CubicFirstMoment

end

end OAI
