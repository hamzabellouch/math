import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeyl
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionInvolutive

namespace OAI

/-! Involutivity of the actual conjugated inversion, on both the
arithmetic root subgroup and positive-height points. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeylConjugate_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    ((cubicThetaPrimeRootWeylConjugate hp g).val.val : Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/p^2);-p^2*g.val.val 0 1,g.val.val 0 0] :=
  cubicThetaPrimeRootWeyl_matrix hp g

theorem cubicThetaPrimeRootWeylConjugate_involutive {p : Eisenstein} (hp : primaryPrime p) :
    Function.Involutive (cubicThetaPrimeRootWeylConjugate hp) := by
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [cubicThetaPrimeRootWeylConjugate_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 1)
      (cubicThetaPrimeRootWeylConjugate_matrix hp g)
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 0)
      (cubicThetaPrimeRootWeylConjugate_matrix hp g)
    simp at he ⊢
    rw [he,show -(p^2*g.val.val 0 1)=p^2*(-g.val.val 0 1) by ring,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 hp.2.ne_zero),neg_neg]
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 1)
      (cubicThetaPrimeRootWeylConjugate_matrix hp g)
    simp at he ⊢
    rw [he]
    linear_combination cubicThetaPrimeRoot_lower_division hp g
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 0)
      (cubicThetaPrimeRootWeylConjugate_matrix hp g)

lemma cubicThetaPrimeRootWeylElement_inversion {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootWeylElement hp=cubicThetaInversionMatrix (p:ℂ)
      (fun he => hp.2.ne_zero (Subtype.ext he)) := by
  rw [cubicThetaPrimeRootWeylElement,cubicThetaPrimeAtkinMatrix,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change ((cubicThetaInversionMatrix 1 one_ne_zero:Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaPrimeDilation hp.2.ne_zero:Matrix (Fin 2) (Fin 2) ℂ))*
      (cubicThetaPrimeDilation hp.2.ne_zero:Matrix (Fin 2) (Fin 2) ℂ)=_
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaInversionMatrix,cubicThetaPrimeDilation,Matrix.mul_apply,Fin.sum_univ_two,
      ←pow_two,cubicThetaPrimeSquareRoot_sq]

lemma cubicThetaPrimeRootWeylPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) (y : CubicThetaPoint) :
    cubicThetaPrimeRootWeylElement hp • (g.val • y)=
      (cubicThetaPrimeRootWeylConjugate hp g).val • (cubicThetaPrimeRootWeylElement hp • y) := by
  change cubicThetaPrimeRootWeylElement hp • (cubicThetaPrincipalComplex g.val • y)=
    cubicThetaPrincipalComplex (cubicThetaPrimeRootWeylConjugate hp g).val •
      (cubicThetaPrimeRootWeylElement hp • y)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeRootWeyl_intertwines]

lemma cubicThetaPrimeRootWeylPoint_involutive {p : Eisenstein} (hp : primaryPrime p)
    (y : CubicThetaPoint) :
    cubicThetaPrimeRootWeylElement hp • (cubicThetaPrimeRootWeylElement hp • y)=y := by
  apply Subtype.ext
  change cubicThetaMobius (cubicThetaPrimeRootWeylElement hp)
    (cubicThetaMobius (cubicThetaPrimeRootWeylElement hp) y.val)=y.val
  rw [cubicThetaPrimeRootWeylElement_inversion,
    cubicThetaMobius_inversion _ (cubicThetaMobius_height_pos _ y.property),
    cubicThetaMobius_inversion _ y.property]
  exact cubicThetaInversion_involutive (fun he => hp.2.ne_zero (Subtype.ext he)) y.property

end CubicFirstMoment

end

end OAI
