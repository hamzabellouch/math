import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootSubgroup

namespace OAI

/-! Integral formulas for conjugation by the fractional upper root 3x/p.
The defining congruences give actual integral quotients. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeRoot_lower_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    p^2*(g.val.val 1 0/p^2)=g.val.val 1 0 :=
  EuclideanDomain.mul_div_cancel' (pow_ne_zero 2 hp.2.ne_zero) g.property.1

lemma cubicThetaPrimeRoot_diagonal_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    p*((g.val.val 1 1-g.val.val 0 0)/p)=g.val.val 1 1-g.val.val 0 0 :=
  EuclideanDomain.mul_div_cancel' hp.2.ne_zero (by simpa only [neg_sub] using dvd_neg.mpr g.property.2)

def cubicThetaPrimeRootMatrix {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) : SL(2,Eisenstein) := by
  let C := g.val.val 1 0/p^2
  let D := (g.val.val 1 1-g.val.val 0 0)/p
  refine ⟨!![g.val.val 0 0+3*x*p*C,g.val.val 0 1+3*x*D-9*x^2*C;
    g.val.val 1 0,g.val.val 1 1-3*x*p*C],?_⟩
  rw [Matrix.det_fin_two_of]
  have hC : p^2*C=g.val.val 1 0 := cubicThetaPrimeRoot_lower_division hp g
  have hD : g.val.val 1 1=g.val.val 0 0+p*D := by
    have he := cubicThetaPrimeRoot_diagonal_division hp g
    dsimp only [D]
    linear_combination -he
  calc
    _ = g.val.val 0 0*g.val.val 1 1-g.val.val 0 1*g.val.val 1 0 := by
      rw [hD,←hC]
      ring
    _ = 1 := cubicThetaPrincipalGroup_det g.val

lemma cubicThetaPrimeRootMatrix_mem {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaPrimeRootMatrix hp x g∈cubicThetaPrincipalGroup := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary g.val).1
  have hd := (cubicThetaPrincipalGroup_diagonal_primary g.val).2
  have hb := (cubicThetaPrincipalGroup_offDiagonal g.val).1
  have hc := (cubicThetaPrincipalGroup_offDiagonal g.val).2
  let C := g.val.val 1 0/p^2
  let D := (g.val.val 1 1-g.val.val 0 0)/p
  have ht : (3:Eisenstein)∣3*x*p*C := ⟨x*p*C,by ring⟩
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (g.val.val 0 0+3*x*p*C) ∧
    (3:Eisenstein)∣g.val.val 0 1+3*x*D-9*x^2*C ∧
    (3:Eisenstein)∣g.val.val 1 0 ∧ primary (g.val.val 1 1-3*x*p*C)
  refine ⟨?_,?_,hc,?_⟩
  · change (3:Eisenstein)∣(g.val.val 0 0+3*x*p*C)-1
    convert dvd_add ha ht using 1; ring
  · exact dvd_sub (dvd_add hb ⟨x*D,by ring⟩) ⟨3*x^2*C,by ring⟩
  · change (3:Eisenstein)∣(g.val.val 1 1-3*x*p*C)-1
    convert dvd_sub hd ht using 1; ring

def cubicThetaPrimeRootConjugate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) : cubicThetaPrimeRootSubgroup p :=
  ⟨⟨cubicThetaPrimeRootMatrix hp x g,cubicThetaPrimeRootMatrix_mem hp x g⟩,by
    refine ⟨g.property.1,?_⟩
    change p∣(g.val.val 0 0+3*x*p*(g.val.val 1 0/p^2))-
      (g.val.val 1 1-3*x*p*(g.val.val 1 0/p^2))
    convert dvd_add g.property.2 (show p∣6*x*p*(g.val.val 1 0/p^2) from
      ⟨6*x*(g.val.val 1 0/p^2),by ring⟩) using 1; ring⟩

end CubicFirstMoment

end

end OAI
