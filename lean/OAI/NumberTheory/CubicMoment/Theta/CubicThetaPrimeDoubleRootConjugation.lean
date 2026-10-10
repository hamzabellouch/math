import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootMatrix
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootCharacter

namespace OAI

/-! Integral conjugation at the square root scale. The cubic twist of
the dilation is trivial, so the original multiplier is retained exactly. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimeDoubleRootIwahori {p : Eisenstein} (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaPrimeIwahori (p^2) :=
  ⟨g.val,(dvd_pow_self (p^2) (by decide : 2≠0)).trans g.property.1⟩

lemma cubicThetaPrimeDoubleRoot_lower_single_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    g.val.val 1 0/p^2=p^2*(g.val.val 1 0/(p^2)^2) := by
  apply mul_left_cancel₀ (pow_ne_zero 2 hp.2.ne_zero)
  have hh : p^2*(g.val.val 1 0/p^2)=g.val.val 1 0 :=
    EuclideanDomain.mul_div_cancel' (pow_ne_zero 2 hp.2.ne_zero)
      ((dvd_pow_self (p^2) (by decide : 2≠0)).trans g.property.1)
  rw [hh]
  have he := cubicThetaPrimeDoubleRoot_lower_division hp g
  linear_combination -he

theorem cubicThetaPrimeDoubleRootConjugate_dilation {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleRootIwahori (cubicThetaPrimeDoubleRootConjugate hp x g))=
      cubicThetaPrincipalTranslation x*cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
        (cubicThetaPrimeDoubleRootIwahori g)*(cubicThetaPrincipalTranslation x)⁻¹ := by
  let a := g.val.val 0 0
  let b := g.val.val 0 1
  let c := g.val.val 1 0
  let d := g.val.val 1 1
  let C := c/(p^2)^2
  let B := (d-a)/p^2
  have hc : c/p^2=p^2*C := cubicThetaPrimeDoubleRoot_lower_single_division hp g
  have hd : p^2*B=d-a := cubicThetaPrimeDoubleRoot_diagonal_division hp g
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  dsimp only [cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,
    cubicThetaPrimeDoubleRootIwahori,cubicThetaPrimeDoubleRootConjugate,cubicThetaPrimeDoubleRootMatrix,
    cubicThetaPrincipalTranslation]
  simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,neg_zero]
  change (!![a+3*x*p^2*C,p^2*(b+3*x*B-9*x^2*C);c/p^2,d-3*x*p^2*C] :
    Matrix (Fin 2) (Fin 2) Eisenstein)=
    !![1,3*x;0,1]*!![a,p^2*b;c/p^2,d]*!![1,-(3*x);0,1]
  rw [hc]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring_nf
  linear_combination (3*x:Eisenstein)*hd

lemma cubicThetaPrimeDoubleRoot_diagonal_character {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) : cubicSymbol p (g.val.val 0 0)=1 := by
  have hc : p^2∣g.val.val 1 0 := (dvd_pow_self (p^2) (by decide : 2≠0)).trans g.property.1
  have hd : p∣g.val.val 0 0-g.val.val 1 1 := (dvd_pow_self p (by decide : 2≠0)).trans g.property.2
  exact cubicThetaPrimeRoot_diagonal_character hp (⟨g.val,hc,hd⟩ : cubicThetaPrimeRootSubgroup p)

lemma cubicThetaPrimeDoubleRootDilation_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleRootIwahori g))=cubicThetaKubotaValue g.val := by
  have he := cubicThetaPrimePowerConjugate_kubota_star hp 2 (cubicThetaPrimeDoubleRootIwahori g)
  change cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeDoubleRootIwahori g))=
    star ((cubicSymbol p (g.val.val 0 0))^2)*cubicThetaKubotaValue g.val at he
  rw [cubicThetaPrimeDoubleRoot_diagonal_character hp g,one_pow,star_one,one_mul] at he
  exact he

theorem cubicThetaPrimeDoubleRootConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeDoubleRootConjugate hp x g).val=
      cubicThetaKubotaValue g.val := by
  have hM : cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleRootIwahori (cubicThetaPrimeDoubleRootConjugate hp x g)))=
      cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
        (cubicThetaPrimeDoubleRootIwahori g)) := by
    rw [cubicThetaPrimeDoubleRootConjugate_dilation,cubicThetaKubotaValue_mul,
      cubicThetaKubotaValue_mul,cubicThetaPrincipalTranslation_value,
      cubicThetaPrincipalTranslation_inverse_value,one_mul,mul_one]
  exact (cubicThetaPrimeDoubleRootDilation_kubota hp
    (cubicThetaPrimeDoubleRootConjugate hp x g)).symm.trans
      (hM.trans (cubicThetaPrimeDoubleRootDilation_kubota hp g))

end CubicFirstMoment

end

end OAI
