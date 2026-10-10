import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootSubgroup
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeConjugation

namespace OAI

/-! The exact arithmetic subgroup for translations by 3x/p^3.
It is needed to compare the cubic Hecke correlation with finite Fourier classes. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

abbrev cubicThetaPrimeCubeRootSubgroup (p : Eisenstein) := cubicThetaPrimeRootSubgroup (p^3)

lemma cubicThetaPrimeCubeRootSubgroup_finiteIndex {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeCubeRootSubgroup p).FiniteIndex :=
  cubicThetaPrimeRootSubgroup_finiteIndex (pow_ne_zero 3 hp.2.ne_zero)

lemma cubicThetaPrimeCubeRoot_lower_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    (p^3)^2*(g.val.val 1 0/(p^3)^2)=g.val.val 1 0 :=
  EuclideanDomain.mul_div_cancel' (pow_ne_zero 2 (pow_ne_zero 3 hp.2.ne_zero)) g.property.1

lemma cubicThetaPrimeCubeRoot_diagonal_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    p^3*((g.val.val 1 1-g.val.val 0 0)/p^3)=g.val.val 1 1-g.val.val 0 0 :=
  EuclideanDomain.mul_div_cancel' (pow_ne_zero 3 hp.2.ne_zero)
    (by simpa only [neg_sub] using dvd_neg.mpr g.property.2)

def cubicThetaPrimeCubeRootMatrix {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) : SL(2,Eisenstein) := by
  let C := g.val.val 1 0/(p^3)^2
  let D := (g.val.val 1 1-g.val.val 0 0)/p^3
  refine ⟨!![g.val.val 0 0+3*x*p^3*C,g.val.val 0 1+3*x*D-9*x^2*C;
    g.val.val 1 0,g.val.val 1 1-3*x*p^3*C],?_⟩
  rw [Matrix.det_fin_two_of]
  have hC : (p^3)^2*C=g.val.val 1 0 := cubicThetaPrimeCubeRoot_lower_division hp g
  have hD : g.val.val 1 1=g.val.val 0 0+p^3*D := by
    have he := cubicThetaPrimeCubeRoot_diagonal_division hp g
    dsimp only [D]
    linear_combination -he
  calc
    _ = g.val.val 0 0*g.val.val 1 1-g.val.val 0 1*g.val.val 1 0 := by
      rw [hD,←hC]
      ring
    _ = 1 := cubicThetaPrincipalGroup_det g.val

lemma cubicThetaPrimeCubeRootMatrix_mem {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaPrimeCubeRootMatrix hp x g∈cubicThetaPrincipalGroup := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary g.val).1
  have hd := (cubicThetaPrincipalGroup_diagonal_primary g.val).2
  have hb := (cubicThetaPrincipalGroup_offDiagonal g.val).1
  have hc := (cubicThetaPrincipalGroup_offDiagonal g.val).2
  let C := g.val.val 1 0/(p^3)^2
  let D := (g.val.val 1 1-g.val.val 0 0)/p^3
  have ht : (3:Eisenstein)∣3*x*p^3*C := ⟨x*p^3*C,by ring⟩
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (g.val.val 0 0+3*x*p^3*C) ∧
    (3:Eisenstein)∣g.val.val 0 1+3*x*D-9*x^2*C ∧
    (3:Eisenstein)∣g.val.val 1 0 ∧ primary (g.val.val 1 1-3*x*p^3*C)
  refine ⟨?_,?_,hc,?_⟩
  · change (3:Eisenstein)∣(g.val.val 0 0+3*x*p^3*C)-1
    convert dvd_add ha ht using 1; ring
  · exact dvd_sub (dvd_add hb ⟨x*D,by ring⟩) ⟨3*x^2*C,by ring⟩
  · change (3:Eisenstein)∣(g.val.val 1 1-3*x*p^3*C)-1
    convert dvd_sub hd ht using 1; ring

def cubicThetaPrimeCubeRootConjugate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) : cubicThetaPrimeCubeRootSubgroup p :=
  ⟨⟨cubicThetaPrimeCubeRootMatrix hp x g,cubicThetaPrimeCubeRootMatrix_mem hp x g⟩,by
    refine ⟨g.property.1,?_⟩
    change p^3∣(g.val.val 0 0+3*x*p^3*(g.val.val 1 0/(p^3)^2))-
      (g.val.val 1 1-3*x*p^3*(g.val.val 1 0/(p^3)^2))
    convert dvd_add g.property.2 (show p^3∣6*x*p^3*(g.val.val 1 0/(p^3)^2) from
      ⟨6*x*(g.val.val 1 0/(p^3)^2),by ring⟩) using 1; ring⟩

end CubicFirstMoment

end

end OAI
