import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHeckeFormula
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeAtkinAction

namespace OAI

/-! The cubed-prime Atkin involution preserves the original multiplier
on the full Iwahori subgroup; no auxiliary character kernel is needed. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeCubeAtkinConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^3)) : cubicThetaPrimeIwahori (p^3) :=
  ⟨cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
      (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g),by
    have he := (cubicThetaInversionConjugate_entries
      (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g)).2
    change p^3∣(cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
      (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g)).val 1 0
    rw [he]
    change p^3∣-(p^3*g.val.val 0 1)
    exact dvd_neg.mpr (dvd_mul_right _ _)⟩

lemma cubicThetaPrimeCubeAtkinConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^3)) :
    cubicThetaKubotaValue (cubicThetaPrimeCubeAtkinConjugate hp g).val=
      cubicThetaKubotaValue g.val := by
  change cubicThetaKubotaValue (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
    (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g))=_
  rw [cubicThetaInversionConjugate_character]
  exact (cubicThetaPrimeCubeConjugate_kubota hp g).symm

lemma cubicThetaPrimeCubeAtkinConjugate_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^3)) :
    ((cubicThetaPrimeCubeAtkinConjugate hp g).val.val : Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/p^3);-p^3*g.val.val 0 1,g.val.val 0 0] := by
  change (((cubicThetaFullInversion⁻¹)⁻¹*
    cubicThetaPrimeConjugatedMatrix (primary_ne_zero (cubicThetaPrimeCube_primary hp)) g*
      cubicThetaFullInversion⁻¹ : SL(2,Eisenstein)) : Matrix (Fin 2) (Fin 2) Eisenstein)=_
  rw [inv_inv,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  simp [cubicThetaFullInversion,cubicThetaPrimeConjugatedMatrix,Matrix.adjugate_fin_two]

theorem cubicThetaPrimeCubeAtkinConjugate_involutive {p : Eisenstein}
    (hp : primaryPrime p) : Function.Involutive (cubicThetaPrimeCubeAtkinConjugate hp) := by
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [cubicThetaPrimeCubeAtkinConjugate_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 1)
      (cubicThetaPrimeCubeAtkinConjugate_matrix hp g)
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 0)
      (cubicThetaPrimeCubeAtkinConjugate_matrix hp g)
    simp at he ⊢
    rw [he,show -(p^3*g.val.val 0 1)=p^3*(-g.val.val 0 1) by ring,
      mul_div_cancel_left₀ _ (pow_ne_zero 3 hp.2.ne_zero),neg_neg]
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 1)
      (cubicThetaPrimeCubeAtkinConjugate_matrix hp g)
    simp at he ⊢
    rw [he]
    linear_combination cubicThetaPrimeIwahori_division (pow_ne_zero 3 hp.2.ne_zero) g
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 0)
      (cubicThetaPrimeCubeAtkinConjugate_matrix hp g)

def cubicThetaPrimeCubeAtkinMatrix {p : Eisenstein} (hp : primaryPrime p) : SL(2,ℂ) :=
  cubicThetaFullComplex cubicThetaFullInversion*cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)

theorem cubicThetaPrimeCubeAtkinMatrix_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^3)) :
    cubicThetaPrimeCubeAtkinMatrix hp*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeCubeAtkinConjugate hp g).val*
        cubicThetaPrimeCubeAtkinMatrix hp := by
  have he : cubicThetaPrincipalComplex (cubicThetaPrimeCubeAtkinConjugate hp g).val=
      cubicThetaFullComplex cubicThetaFullInversion*
        cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g)*
          (cubicThetaFullComplex cubicThetaFullInversion)⁻¹ := by
    change cubicThetaFullComplex ((cubicThetaFullInversion⁻¹)⁻¹*
      (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g).val*cubicThetaFullInversion⁻¹)=_
    rw [inv_inv,map_mul,map_mul,map_inv]
    rfl
  rw [cubicThetaPrimeCubeAtkinMatrix,mul_assoc,
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeCube_primary hp) g,he]
  group

end CubicFirstMoment

end

end OAI
