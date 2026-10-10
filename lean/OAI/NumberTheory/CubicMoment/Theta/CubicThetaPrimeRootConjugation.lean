import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootMatrix
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinCusp

namespace OAI

/-! The integral root matrix is conjugation by an actual upper translation
after the prime dilation. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimeRootIwahori {p : Eisenstein} (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaPrimeIwahori p :=
  ⟨g.val,(dvd_pow_self p (by decide : 2≠0)).trans g.property.1⟩

lemma cubicThetaPrimeRoot_lower_single_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    g.val.val 1 0/p=p*(g.val.val 1 0/p^2) := by
  apply mul_left_cancel₀ hp.2.ne_zero
  have hh : p*(g.val.val 1 0/p)=g.val.val 1 0 :=
    EuclideanDomain.mul_div_cancel' hp.2.ne_zero
      ((dvd_pow_self p (by decide : 2≠0)).trans g.property.1)
  rw [hh]
  have he := cubicThetaPrimeRoot_lower_division hp g
  linear_combination -he

theorem cubicThetaPrimeRootConjugate_dilation {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeRootIwahori (cubicThetaPrimeRootConjugate hp x g))=
      cubicThetaPrincipalTranslation x*cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeRootIwahori g)*
        (cubicThetaPrincipalTranslation x)⁻¹ := by
  let a := g.val.val 0 0
  let b := g.val.val 0 1
  let c := g.val.val 1 0
  let d := g.val.val 1 1
  let C := c/p^2
  let B := (d-a)/p
  have hc : c/p=p*C := cubicThetaPrimeRoot_lower_single_division hp g
  have hd : p*B=d-a := cubicThetaPrimeRoot_diagonal_division hp g
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  dsimp only [cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,
    cubicThetaPrimeRootIwahori,cubicThetaPrimeRootConjugate,cubicThetaPrimeRootMatrix,
    cubicThetaPrincipalTranslation]
  simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,neg_zero]
  change (!![a+3*x*p*C,p*(b+3*x*B-9*x^2*C);c/p,d-3*x*p*C] :
    Matrix (Fin 2) (Fin 2) Eisenstein)=
    !![1,3*x;0,1]*!![a,p*b;c/p,d]*!![1,-(3*x);0,1]
  rw [hc]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring_nf
  linear_combination (3*x:Eisenstein)*hd

end CubicFirstMoment

end

end OAI
