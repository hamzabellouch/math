import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeTraceExpansion
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimePowerFourier

namespace OAI

/-! Primitive rows that triangularize the three nonzero valuation
branches of the cubed-prime lower chart. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeReduction_primary {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) : primary (p^(3-k.val)) := by
  fin_cases k
  · exact cubicThetaPrimeCube_primary hp
  · change primary (p^2)
    simpa only [pow_two] using primary_mul hp.1 hp.1
  · simpa only [Nat.reduceSub,pow_one] using hp.1

def cubicThetaPrimeCubeReductionRow {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) : CubicThetaBottomRow where
  c := -3*n
  d := p^(3-k.val)
  c_three := ⟨-n,by ring⟩
  d_primary := cubicThetaPrimeCubeReduction_primary hp k
  coprime := by
    simpa only [neg_mul] using
      ((primary_coprime_three (cubicThetaPrimeCubeReduction_primary hp k)).symm.mul_left
        ((hp.2.coprime_iff_not_dvd.mpr hn).symm.pow_right)).neg_left

def cubicThetaPrimeCubeReduction {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) : cubicThetaPrincipalGroup :=
  (cubicThetaPrimeCubeReductionRow hp k n hn).completion

lemma cubicThetaPrimeCubeReduction_c {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    (cubicThetaPrimeCubeReduction hp k n hn).val 1 0= -3*n :=
  congrArg CubicThetaBottomRow.c (cubicThetaPrimeCubeReductionRow hp k n hn).completion_row

lemma cubicThetaPrimeCubeReduction_d {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    (cubicThetaPrimeCubeReduction hp k n hn).val 1 1=p^(3-k.val) :=
  congrArg CubicThetaBottomRow.d (cubicThetaPrimeCubeReductionRow hp k n hn).completion_row

lemma cubicThetaPrimeCubeReduction_determinant {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    (cubicThetaPrimeCubeReduction hp k n hn).val 0 0*p^(3-k.val)+
      3*n*(cubicThetaPrimeCubeReduction hp k n hn).val 0 1=1 := by
  have he := cubicThetaPrincipalGroup_det (cubicThetaPrimeCubeReduction hp k n hn)
  rw [cubicThetaPrimeCubeReduction_c,cubicThetaPrimeCubeReduction_d] at he
  linear_combination he

lemma cubicThetaPrimeCubeReduction_phase {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    star (cubicThetaKubotaValue (cubicThetaPrimeCubeReduction hp k n hn))=
      (cubicSymbol p (3*n))^(3-k.val) := by
  rw [cubicThetaKubotaValue_bottomRow]
  change star (star (cubicSymbol ((cubicThetaPrimeCubeReduction hp k n hn).val 1 1)
    ((cubicThetaPrimeCubeReduction hp k n hn).val 1 0)))=_
  rw [cubicThetaPrimeCubeReduction_c,cubicThetaPrimeCubeReduction_d,
    star_star,cubicThetaSymbol_prime_pow hp]
  rw [show -3*n= -(3*n) by ring,cubicSymbol_neg hp.1]

end CubicFirstMoment

end

end OAI
