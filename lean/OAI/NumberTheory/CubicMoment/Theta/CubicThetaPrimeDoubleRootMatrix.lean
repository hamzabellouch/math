import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootSubgroup
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootPowerCharacter

namespace OAI

/-! The exact arithmetic subgroup for translations by 3x/p^2.
It is needed to compare the intermediate correlation with finite Fourier classes. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeDouble_primary {p : Eisenstein} (hp : primaryPrime p) : primary (p^2) :=
  cubicThetaPrimePower_primary hp 2

abbrev cubicThetaPrimeDoubleRootSubgroup (p : Eisenstein) := cubicThetaPrimeRootSubgroup (p^2)

lemma cubicThetaPrimeDoubleRootSubgroup_finiteIndex {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeDoubleRootSubgroup p).FiniteIndex :=
  cubicThetaPrimeRootSubgroup_finiteIndex (pow_ne_zero 2 hp.2.ne_zero)

lemma cubicThetaPrimeDoubleRoot_lower_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    (p^2)^2*(g.val.val 1 0/(p^2)^2)=g.val.val 1 0 :=
  EuclideanDomain.mul_div_cancel' (pow_ne_zero 2 (pow_ne_zero 2 hp.2.ne_zero)) g.property.1

lemma cubicThetaPrimeDoubleRoot_diagonal_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    p^2*((g.val.val 1 1-g.val.val 0 0)/p^2)=g.val.val 1 1-g.val.val 0 0 :=
  EuclideanDomain.mul_div_cancel' (pow_ne_zero 2 hp.2.ne_zero)
    (by simpa only [neg_sub] using dvd_neg.mpr g.property.2)

def cubicThetaPrimeDoubleRootMatrix {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) : SL(2,Eisenstein) := by
  let C := g.val.val 1 0/(p^2)^2
  let D := (g.val.val 1 1-g.val.val 0 0)/p^2
  refine ⟨!![g.val.val 0 0+3*x*p^2*C,g.val.val 0 1+3*x*D-9*x^2*C;
    g.val.val 1 0,g.val.val 1 1-3*x*p^2*C],?_⟩
  rw [Matrix.det_fin_two_of]
  have hC : (p^2)^2*C=g.val.val 1 0 := cubicThetaPrimeDoubleRoot_lower_division hp g
  have hD : g.val.val 1 1=g.val.val 0 0+p^2*D := by
    have he := cubicThetaPrimeDoubleRoot_diagonal_division hp g
    dsimp only [D]
    linear_combination -he
  calc
    _ = g.val.val 0 0*g.val.val 1 1-g.val.val 0 1*g.val.val 1 0 := by
      rw [hD,←hC]
      ring
    _ = 1 := cubicThetaPrincipalGroup_det g.val

lemma cubicThetaPrimeDoubleRootMatrix_mem {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaPrimeDoubleRootMatrix hp x g∈cubicThetaPrincipalGroup := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary g.val).1
  have hd := (cubicThetaPrincipalGroup_diagonal_primary g.val).2
  have hb := (cubicThetaPrincipalGroup_offDiagonal g.val).1
  have hc := (cubicThetaPrincipalGroup_offDiagonal g.val).2
  let C := g.val.val 1 0/(p^2)^2
  let D := (g.val.val 1 1-g.val.val 0 0)/p^2
  have ht : (3:Eisenstein)∣3*x*p^2*C := ⟨x*p^2*C,by ring⟩
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (g.val.val 0 0+3*x*p^2*C) ∧
    (3:Eisenstein)∣g.val.val 0 1+3*x*D-9*x^2*C ∧
    (3:Eisenstein)∣g.val.val 1 0 ∧ primary (g.val.val 1 1-3*x*p^2*C)
  refine ⟨?_,?_,hc,?_⟩
  · change (3:Eisenstein)∣(g.val.val 0 0+3*x*p^2*C)-1
    convert dvd_add ha ht using 1; ring
  · exact dvd_sub (dvd_add hb ⟨x*D,by ring⟩) ⟨3*x^2*C,by ring⟩
  · change (3:Eisenstein)∣(g.val.val 1 1-3*x*p^2*C)-1
    convert dvd_sub hd ht using 1; ring

def cubicThetaPrimeDoubleRootConjugate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) : cubicThetaPrimeDoubleRootSubgroup p :=
  ⟨⟨cubicThetaPrimeDoubleRootMatrix hp x g,cubicThetaPrimeDoubleRootMatrix_mem hp x g⟩,by
    refine ⟨g.property.1,?_⟩
    change p^2∣(g.val.val 0 0+3*x*p^2*(g.val.val 1 0/(p^2)^2))-
      (g.val.val 1 1-3*x*p^2*(g.val.val 1 0/(p^2)^2))
    convert dvd_add g.property.2 (show p^2∣6*x*p^2*(g.val.val 1 0/(p^2)^2) from
      ⟨6*x*(g.val.val 1 0/(p^2)^2),by ring⟩) using 1; ring⟩

end CubicFirstMoment

end

end OAI
