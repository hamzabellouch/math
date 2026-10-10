import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootConjugation

namespace OAI

/-! The fractional root conjugation preserves the actual cubic Kubota
multiplier on its arithmetic subgroup. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrincipalTranslation_inverse_value (x : Eisenstein) :
    cubicThetaKubotaValue (cubicThetaPrincipalTranslation x)⁻¹=1 := by
  have he := cubicThetaKubotaCharacter.map_mul (cubicThetaPrincipalTranslation x)
    (cubicThetaPrincipalTranslation x)⁻¹
  rw [mul_inv_cancel,map_one] at he
  change 1=cubicThetaKubotaValue (cubicThetaPrincipalTranslation x)*
    cubicThetaKubotaValue (cubicThetaPrincipalTranslation x)⁻¹ at he
  rw [cubicThetaPrincipalTranslation_value,one_mul] at he
  exact he.symm

lemma cubicThetaPrimeRootConjugate_diagonal_character {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) :
    cubicSymbol p ((cubicThetaPrimeRootConjugate hp x g).val.val 0 0)=
      cubicSymbol p (g.val.val 0 0) := by
  apply cubicSymbol_congr
  apply residue_eq_of_dvd_sub
  refine ⟨3*x*(g.val.val 1 0/p^2),?_⟩
  change (g.val.val 0 0+3*x*p*(g.val.val 1 0/p^2))-g.val.val 0 0=_
  ring

theorem cubicThetaPrimeRootConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeRootConjugate hp x g).val=
      cubicThetaKubotaValue g.val := by
  have hM : cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1
      (cubicThetaPrimeRootIwahori (cubicThetaPrimeRootConjugate hp x g)))=
      cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeRootIwahori g)) := by
    rw [cubicThetaPrimeRootConjugate_dilation,cubicThetaKubotaValue_mul,
      cubicThetaKubotaValue_mul,cubicThetaPrincipalTranslation_value,
      cubicThetaPrincipalTranslation_inverse_value,one_mul,mul_one]
  have hleft := cubicThetaPrimeConjugate_kubota hp
    (cubicThetaPrimeRootIwahori (cubicThetaPrimeRootConjugate hp x g))
  change cubicThetaKubotaValue (cubicThetaPrimeRootConjugate hp x g).val=
    cubicSymbol p ((cubicThetaPrimeRootConjugate hp x g).val.val 0 0)*
      cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1
        (cubicThetaPrimeRootIwahori (cubicThetaPrimeRootConjugate hp x g))) at hleft
  rw [cubicThetaPrimeRootConjugate_diagonal_character,hM] at hleft
  exact hleft.trans (cubicThetaPrimeConjugate_kubota hp (cubicThetaPrimeRootIwahori g)).symm

end CubicFirstMoment

end

end OAI
