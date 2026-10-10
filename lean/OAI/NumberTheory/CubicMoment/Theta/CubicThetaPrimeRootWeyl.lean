import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootDiagonal

namespace OAI

/-! The second root direction is supplied by the actual conjugated
inversion. Its integral conjugation preserves the same cubic multiplier. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeyl_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    ((cubicThetaPrimeAtkinConjugate hp (cubicThetaPrimeRootDilationIwahori hp g)).val.val :
      Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/p^2);-p^2*g.val.val 0 1,g.val.val 0 0] := by
  rw [cubicThetaPrimeAtkinConjugate_matrix]
  change (!![g.val.val 1 1,-((g.val.val 1 0/p)/p);-p*(p*g.val.val 0 1),g.val.val 0 0] :
    Matrix (Fin 2) (Fin 2) Eisenstein)=_
  rw [cubicThetaPrimeRoot_lower_single_division hp g,mul_div_cancel_left₀ _ hp.2.ne_zero]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pow_two,mul_assoc]

def cubicThetaPrimeRootWeylConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) : cubicThetaPrimeRootSubgroup p :=
  ⟨(cubicThetaPrimeAtkinConjugate hp (cubicThetaPrimeRootDilationIwahori hp g)).val,by
    change p^2∣(cubicThetaPrimeAtkinConjugate hp (cubicThetaPrimeRootDilationIwahori hp g)).val.val 1 0 ∧
      p∣(cubicThetaPrimeAtkinConjugate hp (cubicThetaPrimeRootDilationIwahori hp g)).val.val 0 0-
        (cubicThetaPrimeAtkinConjugate hp (cubicThetaPrimeRootDilationIwahori hp g)).val.val 1 1
    rw [cubicThetaPrimeRootWeyl_matrix]
    constructor
    · exact ⟨-g.val.val 0 1,by simp⟩
    · simpa using dvd_neg.mpr g.property.2⟩

theorem cubicThetaPrimeRootWeyl_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeRootWeylConjugate hp g).val=cubicThetaKubotaValue g.val := by
  let k : cubicThetaPrimeCharacterKernel hp :=
    ⟨cubicThetaPrimeRootDilationIwahori hp g,by
      change cubicSymbol p (g.val.val 0 0)=1
      exact cubicThetaPrimeRoot_diagonal_character hp g⟩
  change cubicThetaKubotaValue (cubicThetaPrimeAtkinKernel hp k).val.val=_
  exact (cubicThetaPrimeAtkinKernel_kubota hp k).trans (cubicThetaPrimeRootDilation_kubota hp g)

def cubicThetaPrimeRootWeylElement {p : Eisenstein} (hp : primaryPrime p) : SL(2,ℂ) :=
  cubicThetaPrimeAtkinMatrix hp*cubicThetaPrimeDilation hp.2.ne_zero

theorem cubicThetaPrimeRootWeyl_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaPrimeRootWeylElement hp*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeRootWeylConjugate hp g).val*
        cubicThetaPrimeRootWeylElement hp := by
  have hD : cubicThetaPrimeDilation hp.2.ne_zero*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeRootDilationIwahori hp g).val*
        cubicThetaPrimeDilation hp.2.ne_zero :=
    cubicThetaPrimeDilation_intertwines hp.1 (cubicThetaPrimeRootIwahori g)
  have hW : cubicThetaPrimeAtkinMatrix hp*
      cubicThetaPrincipalComplex (cubicThetaPrimeRootDilationIwahori hp g).val=
      cubicThetaPrincipalComplex (cubicThetaPrimeRootWeylConjugate hp g).val*cubicThetaPrimeAtkinMatrix hp :=
    cubicThetaPrimeAtkinMatrix_intertwines hp (cubicThetaPrimeRootDilationIwahori hp g)
  unfold cubicThetaPrimeRootWeylElement
  rw [mul_assoc,hD,←mul_assoc,hW,mul_assoc]

end CubicFirstMoment

end

end OAI
