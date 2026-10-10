import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootWeylSections

namespace OAI

/-! The twice-dilated global branch is fixed by intermediate root translations. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeDoubleRootWeyl_global_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (z : CubicThetaPoint) :
    (cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val z=
      (cubicThetaInversionSection F).val
        (cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero) • (cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero) • z)) := by
  change F.val (cubicThetaPrimeDoubleRootWeylElement hp • z)=_
  rw [cubicThetaPrimeDoubleRootWeylElement,cubicThetaPrimeDoubleAtkinMatrix,mul_smul,mul_smul]
  rfl

lemma cubicThetaPrimeDoubleRootWeyl_global_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : CubicThetaSection) :
    cubicThetaPrimeDoubleRootSectionTranslate hp x
      (cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F))=
        cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F) := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)
  let t := cubicThetaPrincipalTranslation x
  let g : cubicThetaPrimeIwahori (p^2) := ⟨t,by change p^2∣0; exact dvd_zero (p^2)⟩
  have h1 : D*cubicThetaPrimeDoubleRootElement hp x=cubicThetaPrincipalComplex t*D := by
    dsimp only [D,t,cubicThetaPrimeDoubleRootElement]
    group
  have h2 : D*cubicThetaPrincipalComplex t=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g)*D :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeDouble_primary hp) g
  have h3 : D*(D*cubicThetaPrimeDoubleRootElement hp x)=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g)*(D*D) := by
    rw [h1,←mul_assoc,h2,mul_assoc]
  have hk : cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g)=1 := by
    rw [cubicThetaKubotaValue_eq_symbol]
    simp [g,t,cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,
      cubicThetaPrincipalTranslation,cubicSymbol_one_lower]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change (cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val
    (cubicThetaPrimeDoubleRootElement hp x • y)=_
  rw [cubicThetaPrimeDoubleRootWeyl_global_zero,cubicThetaPrimeDoubleRootWeyl_global_zero]
  change (cubicThetaInversionSection F).val (D • (D • (cubicThetaPrimeDoubleRootElement hp x • y)))=
    (cubicThetaInversionSection F).val (D • (D • y))
  rw [←mul_smul,←mul_smul,mul_assoc,h3,mul_smul,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g • (D • (D • y)))=_
  rw [(cubicThetaInversionSection F).property,hk,one_mul]


end CubicFirstMoment

end

end OAI
