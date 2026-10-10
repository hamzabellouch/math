import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylMeasure

namespace OAI

/-! An integral Bruhat representative for two inverse nonzero root
parameters. Its multiplier is the literal cubic residue symbol. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeRootBruhat_division {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) :
    p*((1-9*x*y)/p)=1-9*x*y := by
  apply EuclideanDomain.mul_div_cancel' hp.2.ne_zero
  simpa only [neg_sub] using dvd_neg.mpr hxy

def cubicThetaPrimeRootBruhatMatrix {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) : SL(2,Eisenstein) :=
  ⟨!![p,3*x;-3*y,(1-9*x*y)/p],by
    rw [Matrix.det_fin_two_of]
    linear_combination cubicThetaPrimeRootBruhat_division hp x y hxy⟩

lemma cubicThetaPrimeRootBruhatMatrix_mem {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) :
    cubicThetaPrimeRootBruhatMatrix hp x y hxy∈cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary p ∧ (3:Eisenstein)∣3*x ∧ (3:Eisenstein)∣-3*y ∧ primary ((1-9*x*y)/p)
  refine ⟨hp.1,⟨x,rfl⟩,⟨-y,by ring⟩,?_⟩
  change (3:Eisenstein)∣(1-9*x*y)/p-1
  apply (primary_coprime_three hp.1).symm.dvd_of_dvd_mul_left
  rw [mul_sub,mul_one,cubicThetaPrimeRootBruhat_division hp x y hxy]
  convert dvd_sub (dvd_neg.mpr hp.1) (show (3:Eisenstein)∣9*x*y from ⟨3*x*y,by ring⟩) using 1
  ring

def cubicThetaPrimeRootBruhat {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaPrimeRootBruhatMatrix hp x y hxy,cubicThetaPrimeRootBruhatMatrix_mem hp x y hxy⟩

lemma cubicThetaPrimeRootBruhat_kubota {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) :
    cubicThetaKubotaValue (cubicThetaPrimeRootBruhat hp x y hxy)=cubicSymbol p (3*y) := by
  rw [cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol p (-3*y)=cubicSymbol p (3*y)
  rw [neg_mul,cubicSymbol_neg hp.1]

end CubicFirstMoment

end

end OAI
