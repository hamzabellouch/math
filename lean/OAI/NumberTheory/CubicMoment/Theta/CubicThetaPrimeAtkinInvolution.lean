import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeAtkinConjugation

namespace OAI

/-! The prime normalizer is an actual involution, not just a map of
multiplier values. This supplies the group equivalence for the finite cover. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrimeAtkinConjugate_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) :
    ((cubicThetaPrimeAtkinConjugate hp g).val.val : Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/p);-p*g.val.val 0 1,g.val.val 0 0] := by
  change (((cubicThetaFullInversion⁻¹)⁻¹*
    cubicThetaPrimeConjugatedMatrix (primary_ne_zero hp.1) g*
      cubicThetaFullInversion⁻¹ : SL(2,Eisenstein)) : Matrix (Fin 2) (Fin 2) Eisenstein)=_
  rw [inv_inv,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  simp [cubicThetaFullInversion,cubicThetaPrimeConjugatedMatrix,Matrix.adjugate_fin_two]

theorem cubicThetaPrimeAtkinConjugate_involutive {p : Eisenstein}
    (hp : primaryPrime p) : Function.Involutive (cubicThetaPrimeAtkinConjugate hp) := by
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [cubicThetaPrimeAtkinConjugate_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 1)
        (cubicThetaPrimeAtkinConjugate_matrix hp g)
  · have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 0)
      (cubicThetaPrimeAtkinConjugate_matrix hp g)
    simp at h10 ⊢
    rw [h10,show -(p*g.val.val 0 1)=p*(-g.val.val 0 1) by ring,
      mul_div_cancel_left₀ _ hp.2.ne_zero,neg_neg]
  · have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 1)
      (cubicThetaPrimeAtkinConjugate_matrix hp g)
    simp at h01 ⊢
    rw [h01]
    have hc := cubicThetaPrimeIwahori_division hp.2.ne_zero g
    linear_combination hc
  · simpa using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 0)
        (cubicThetaPrimeAtkinConjugate_matrix hp g)

theorem cubicThetaPrimeAtkinKernel_involutive {p : Eisenstein}
    (hp : primaryPrime p) : Function.Involutive (cubicThetaPrimeAtkinKernel hp) := by
  intro g
  apply Subtype.ext
  exact cubicThetaPrimeAtkinConjugate_involutive hp g.val

def cubicThetaPrimeAtkinKernelEquiv {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCharacterKernel hp ≃ cubicThetaPrimeCharacterKernel hp :=
  (cubicThetaPrimeAtkinKernel_involutive hp).toPerm

end CubicFirstMoment

end

end OAI
