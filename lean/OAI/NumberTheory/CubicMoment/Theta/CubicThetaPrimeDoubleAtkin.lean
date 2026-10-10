import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootMatrix
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeAtkinAction

namespace OAI

/-! The squared-prime Atkin matrix and its exact integral conjugation.
Character invariance is used only on the root subgroup. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeDoubleAtkinConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^2)) : cubicThetaPrimeIwahori (p^2) :=
  ⟨cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
      (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g),by
    have he := (cubicThetaInversionConjugate_entries
      (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g)).2
    change p^2∣(cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
      (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g)).val 1 0
    rw [he]
    change p^2∣-(p^2*g.val.val 0 1)
    exact dvd_neg.mpr (dvd_mul_right _ _)⟩

lemma cubicThetaPrimeDoubleAtkinConjugate_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^2)) :
    ((cubicThetaPrimeDoubleAtkinConjugate hp g).val.val : Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/p^2);-p^2*g.val.val 0 1,g.val.val 0 0] := by
  change (((cubicThetaFullInversion⁻¹)⁻¹*
    cubicThetaPrimeConjugatedMatrix (primary_ne_zero (cubicThetaPrimeDouble_primary hp)) g*
      cubicThetaFullInversion⁻¹ : SL(2,Eisenstein)) : Matrix (Fin 2) (Fin 2) Eisenstein)=_
  rw [inv_inv,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  simp [cubicThetaFullInversion,cubicThetaPrimeConjugatedMatrix,Matrix.adjugate_fin_two]

theorem cubicThetaPrimeDoubleAtkinConjugate_involutive {p : Eisenstein}
    (hp : primaryPrime p) : Function.Involutive (cubicThetaPrimeDoubleAtkinConjugate hp) := by
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [cubicThetaPrimeDoubleAtkinConjugate_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 1)
      (cubicThetaPrimeDoubleAtkinConjugate_matrix hp g)
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 0)
      (cubicThetaPrimeDoubleAtkinConjugate_matrix hp g)
    simp at he ⊢
    rw [he,show -(p^2*g.val.val 0 1)=p^2*(-g.val.val 0 1) by ring,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 hp.2.ne_zero),neg_neg]
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 1)
      (cubicThetaPrimeDoubleAtkinConjugate_matrix hp g)
    simp at he ⊢
    rw [he]
    linear_combination cubicThetaPrimeIwahori_division (pow_ne_zero 2 hp.2.ne_zero) g
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 0)
      (cubicThetaPrimeDoubleAtkinConjugate_matrix hp g)

def cubicThetaPrimeDoubleAtkinMatrix {p : Eisenstein} (hp : primaryPrime p) : SL(2,ℂ) :=
  cubicThetaFullComplex cubicThetaFullInversion*cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)

theorem cubicThetaPrimeDoubleAtkinMatrix_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^2)) :
    cubicThetaPrimeDoubleAtkinMatrix hp*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeDoubleAtkinConjugate hp g).val*
        cubicThetaPrimeDoubleAtkinMatrix hp := by
  have he : cubicThetaPrincipalComplex (cubicThetaPrimeDoubleAtkinConjugate hp g).val=
      cubicThetaFullComplex cubicThetaFullInversion*
        cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g)*
          (cubicThetaFullComplex cubicThetaFullInversion)⁻¹ := by
    change cubicThetaFullComplex ((cubicThetaFullInversion⁻¹)⁻¹*
      (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g).val*cubicThetaFullInversion⁻¹)=_
    rw [inv_inv,map_mul,map_mul,map_inv]
    rfl
  rw [cubicThetaPrimeDoubleAtkinMatrix,mul_assoc,
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeDouble_primary hp) g,he]
  group

end CubicFirstMoment

end

end OAI
