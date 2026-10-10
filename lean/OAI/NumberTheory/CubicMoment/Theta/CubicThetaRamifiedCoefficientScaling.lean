import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedResiduePeriodicity

namespace OAI

/-! Ramified cube scaling agrees with the normalization of the
published arithmetic coefficient on every positive ramified order. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaNormalizedObservedCoefficient_lambda_cube {h : Eisenstein} (hh : h≠0) :
    cubicThetaNormalizedObservedCoefficient (lambdaE^3*h)=
      (1/3:ℂ)*cubicThetaNormalizedObservedCoefficient h := by
  have hN : norm lambdaE=3 := by simpa only [pow_one] using cubicThetaNorm_lambda_pow 1
  unfold cubicThetaNormalizedObservedCoefficient cubicThetaObservedWhittakerCoefficient
  rw [cubicThetaArithmeticFourierResidue_lambda_cube hh,
    cubicThetaPoleWeight_cube_mul lambdaE_prime.ne_zero hh,hN]
  push_cast
  ring

def CubicThetaCoordinates.mulLambdaCube {n : Eisenstein} (R : CubicThetaCoordinates n) :
    CubicThetaCoordinates (lambdaE^3*n) where
  unit := R.unit
  order := R.order+3
  squarefreePart := R.squarefreePart
  cubePart := R.cubePart
  squarefree_primary := R.squarefree_primary
  cube_primary := R.cube_primary
  squarefree := R.squarefree
  numerator_eq := by
    calc
      _ = lambdaE^3*((R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3)) :=
        congrArg (fun a => lambdaE^3*a) R.numerator_eq
      _ = _ := by rw [pow_add]; ring

lemma CubicThetaCoordinates.amplitude_mulLambdaCube {n : Eisenstein} (R : CubicThetaCoordinates n) :
    R.mulLambdaCube.amplitude=(1/3:ℝ)*R.amplitude := by
  have hd : (R.order+3)/3=R.order/3+1 := by omega
  simp only [CubicThetaCoordinates.amplitude,CubicThetaCoordinates.mulLambdaCube,hd,Nat.cast_add,Nat.cast_one]
  have he : (4:ℝ)-(((R.order/3:ℕ):ℝ)+1)=(4-((R.order/3:ℕ):ℝ))-1 := by ring
  rw [he,Real.rpow_sub (by norm_num : (0:ℝ)<3),Real.rpow_one]
  ring

theorem CubicThetaCoordinates.coefficient_mulLambdaCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (hR : 0<R.order) :
    R.mulLambdaCube.coefficient=(1/3:ℂ)*R.coefficient := by
  have hmod : (R.order+3)%3=R.order%3 := by omega
  have hA : ((R.order+3)%3=0 ∧ 3≤R.order+3) ↔ (R.order%3=0 ∧ 3≤R.order) := by omega
  have hB : ((R.order+3)%3=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1)) ↔
      (R.order%3=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1)) := by rw [hmod]
  change (if (R.order+3)%3=0 ∧ 3≤R.order+3 then
      (R.mulLambdaCube.amplitude:ℂ)*cubicThetaUnitPhase R.unit*
        star (cubicThetaTwistedGauss R.squarefreePart ((R.unit:Eisenstein)^4*lambdaE^2))
    else if (R.order+3)%3=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1) then
      (R.mulLambdaCube.amplitude:ℂ)*star (gauss R.squarefreePart) else 0)=_
  simp only [hA,hB,R.amplitude_mulLambdaCube]
  unfold CubicThetaCoordinates.coefficient
  split_ifs <;> push_cast <;> ring

end CubicFirstMoment

end

end OAI
