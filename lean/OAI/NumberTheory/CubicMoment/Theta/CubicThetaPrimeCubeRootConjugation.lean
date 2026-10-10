import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootMatrix
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootCharacter

namespace OAI

/-! Integral conjugation at the cubic root scale. The cubic twist of
the dilation is trivial, so the original multiplier is retained exactly. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootIwahori {p : Eisenstein} (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaPrimeIwahori (p^3) :=
  ⟨g.val,(dvd_pow_self (p^3) (by decide : 2≠0)).trans g.property.1⟩

lemma cubicThetaPrimeCubeRoot_lower_single_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    g.val.val 1 0/p^3=p^3*(g.val.val 1 0/(p^3)^2) := by
  apply mul_left_cancel₀ (pow_ne_zero 3 hp.2.ne_zero)
  have hh : p^3*(g.val.val 1 0/p^3)=g.val.val 1 0 :=
    EuclideanDomain.mul_div_cancel' (pow_ne_zero 3 hp.2.ne_zero)
      ((dvd_pow_self (p^3) (by decide : 2≠0)).trans g.property.1)
  rw [hh]
  have he := cubicThetaPrimeCubeRoot_lower_division hp g
  linear_combination -he

theorem cubicThetaPrimeCubeRootConjugate_dilation {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp)
      (cubicThetaPrimeCubeRootIwahori (cubicThetaPrimeCubeRootConjugate hp x g))=
      cubicThetaPrincipalTranslation x*cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp)
        (cubicThetaPrimeCubeRootIwahori g)*(cubicThetaPrincipalTranslation x)⁻¹ := by
  let a := g.val.val 0 0
  let b := g.val.val 0 1
  let c := g.val.val 1 0
  let d := g.val.val 1 1
  let C := c/(p^3)^2
  let B := (d-a)/p^3
  have hc : c/p^3=p^3*C := cubicThetaPrimeCubeRoot_lower_single_division hp g
  have hd : p^3*B=d-a := cubicThetaPrimeCubeRoot_diagonal_division hp g
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  dsimp only [cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,
    cubicThetaPrimeCubeRootIwahori,cubicThetaPrimeCubeRootConjugate,cubicThetaPrimeCubeRootMatrix,
    cubicThetaPrincipalTranslation]
  simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,neg_zero]
  change (!![a+3*x*p^3*C,p^3*(b+3*x*B-9*x^2*C);c/p^3,d-3*x*p^3*C] :
    Matrix (Fin 2) (Fin 2) Eisenstein)=
    !![1,3*x;0,1]*!![a,p^3*b;c/p^3,d]*!![1,-(3*x);0,1]
  rw [hc]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring_nf
  linear_combination (3*x:Eisenstein)*hd

theorem cubicThetaPrimeCubeRootConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeCubeRootConjugate hp x g).val=
      cubicThetaKubotaValue g.val := by
  have hM : cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp)
      (cubicThetaPrimeCubeRootIwahori (cubicThetaPrimeCubeRootConjugate hp x g)))=
      cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp)
        (cubicThetaPrimeCubeRootIwahori g)) := by
    rw [cubicThetaPrimeCubeRootConjugate_dilation,cubicThetaKubotaValue_mul,
      cubicThetaKubotaValue_mul,cubicThetaPrincipalTranslation_value,
      cubicThetaPrincipalTranslation_inverse_value,one_mul,mul_one]
  exact (cubicThetaPrimeCubeConjugate_kubota hp
    (cubicThetaPrimeCubeRootIwahori (cubicThetaPrimeCubeRootConjugate hp x g))).trans
      (hM.trans (cubicThetaPrimeCubeConjugate_kubota hp (cubicThetaPrimeCubeRootIwahori g)).symm)

end CubicFirstMoment

end

end OAI
