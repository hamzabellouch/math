import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeIwahori
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBottomRow

namespace OAI

/-! The integral prime correspondence on the actual level-three group.
Conjugation has its exact cubic diagonal twist, including zero lower-left entries. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrimeIwahori_division {p : Eisenstein} (hp : p≠0)
    (g : cubicThetaPrimeIwahori p) :
    p*(g.val.val 1 0/p)=g.val.val 1 0 :=
  EuclideanDomain.mul_div_cancel' hp g.property

def cubicThetaPrimeConjugatedMatrix {p : Eisenstein} (hp : p≠0)
    (g : cubicThetaPrimeIwahori p) : SL(2,Eisenstein) where
  val := !![g.val.val 0 0,p*g.val.val 0 1;g.val.val 1 0/p,g.val.val 1 1]
  property := by
    simp [Matrix.det_fin_two]
    calc
      _ = g.val.val 0 0*g.val.val 1 1-g.val.val 0 1*g.val.val 1 0 := by
        linear_combination -(g.val.val 0 1)*(cubicThetaPrimeIwahori_division hp g)
      _ = 1 := cubicThetaPrincipalGroup_det g.val

lemma cubicThetaPrimeConjugatedMatrix_mem {p : Eisenstein} (hp : primary p)
    (g : cubicThetaPrimeIwahori p) :
    cubicThetaPrimeConjugatedMatrix (primary_ne_zero hp) g∈cubicThetaPrincipalGroup := by
  have hd := cubicThetaPrincipalGroup_diagonal_primary g.val
  have ho := cubicThetaPrincipalGroup_offDiagonal g.val
  have hc : (3:Eisenstein)∣g.val.val 1 0/p :=
    (primary_coprime_three hp).symm.dvd_of_dvd_mul_left
      (by rw [cubicThetaPrimeIwahori_division (primary_ne_zero hp) g]; exact ho.2)
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (g.val.val 0 0) ∧ (3:Eisenstein)∣p*g.val.val 0 1 ∧
    (3:Eisenstein)∣g.val.val 1 0/p ∧ primary (g.val.val 1 1)
  exact ⟨hd.1,dvd_mul_of_dvd_right ho.1 p,hc,hd.2⟩

def cubicThetaPrimeConjugate {p : Eisenstein} (hp : primary p)
    (g : cubicThetaPrimeIwahori p) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaPrimeConjugatedMatrix (primary_ne_zero hp) g,
    cubicThetaPrimeConjugatedMatrix_mem hp g⟩

theorem cubicThetaPrimeConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) :
    cubicThetaKubotaValue g.val=cubicThetaPrimeIwahoriCharacter p hp g*
      cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 g) := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary g.val).1
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol (g.val.val 0 0) (g.val.val 1 0)=
    cubicSymbol p (g.val.val 0 0)*cubicSymbol (g.val.val 0 0) (g.val.val 1 0/p)
  conv_lhs => rw [←cubicThetaPrimeIwahori_division hp.2.ne_zero g]
  rw [cubicSymbol_mul_upper ha,cubic_reciprocity ha hp.1]

end CubicFirstMoment

end

end OAI
