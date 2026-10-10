import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCommonCuspCoefficient
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSupport

namespace OAI

/-! Removing a primary cube scales the actual three-cusp coefficient by
its norm. This includes all zero-extension cases. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

theorem cubicThetaArithmeticCoefficient_primaryCube (d : Eisenstein) (hd : primary d)
    (n : Eisenstein) :
    cubicThetaArithmeticCoefficient (n*d^3)=
      (norm d:ℂ)⁻¹*cubicThetaArithmeticCoefficient n := by
  revert n
  apply primary_induction (b:=d) ?_ ?_ hd
  · intro n
    have h1 : norm (1:Eisenstein)=1 := by norm_num [norm]
    simp only [one_pow,mul_one,h1,Complex.ofReal_one,inv_one,one_mul]
  · intro p b hp hb ih n
    rw [show n*(p*b)^3=(n*p^3)*b^3 by ring,ih,
      cubicThetaArithmeticCoefficient_primeCube hp,norm_mul_eq,Complex.ofReal_mul,mul_inv_rev]
    ring

lemma cubicThetaShiftedLatticeCoefficient_primaryCube (j : ℤ) (d : Eisenstein)
    (hd : primary d) (n : Eisenstein) :
    cubicThetaShiftedLatticeCoefficient j (n*d^3)=
      (norm d:ℂ)⁻¹*cubicThetaShiftedLatticeCoefficient j n := by
  have hp : primary (d^3) := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using primary_mul hd (primary_mul hd hd)
  have hl3 : lambdaE∣(3:Eisenstein) := ⟨-lambdaE,by
    rw [mul_neg,←pow_two,lambdaE_sq,neg_neg]⟩
  have hl : lambdaE∣n*d^3-n := by
    have H := dvd_mul_of_dvd_right (dvd_trans hl3 hp) n
    convert H using 1
    ring
  have hi : lambdaE∣n*d^3-(j:Eisenstein) ↔ lambdaE∣n-(j:Eisenstein) := by
    constructor
    · intro h
      convert dvd_sub h hl using 1
      ring
    · intro h
      convert dvd_add h hl using 1
      ring
  unfold cubicThetaShiftedLatticeCoefficient
  rw [hi]
  split_ifs
  · rw [show 3*(lambdaE*(n*d^3))=(3*(lambdaE*n))*d^3 by ring,
      cubicThetaArithmeticCoefficient_primaryCube d hd]
    ring
  · ring

lemma cubicThetaActualCuspCoefficient_primaryCube (j : ℤ) (d : Eisenstein)
    (hd : primary d) (n : Eisenstein) :
    cubicThetaActualCuspCoefficient j (n*d^3)=
      (norm d:ℂ)⁻¹*cubicThetaActualCuspCoefficient j n := by
  unfold cubicThetaActualCuspCoefficient
  split_ifs
  · exact cubicThetaArithmeticCoefficient_primaryCube d hd n
  · exact cubicThetaShiftedLatticeCoefficient_primaryCube j d hd n

theorem cubicThetaCommonCuspCoefficient_primaryCube (d : Eisenstein)
    (hd : primary d) (n : Eisenstein) :
    cubicThetaCommonCuspCoefficient (n*d^3)=
      (norm d:ℂ)⁻¹*cubicThetaCommonCuspCoefficient n := by
  unfold cubicThetaCommonCuspCoefficient
  simp_rw [show -(n*d^3)=(-n)*d^3 by ring,
    cubicThetaActualCuspCoefficient_primaryCube _ d hd,star_mul]
  simp only [map_inv₀,Complex.star_def,Complex.conj_ofReal]
  rw [←mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

end CubicFirstMoment

end

end OAI
