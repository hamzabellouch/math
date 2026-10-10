import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDerivativeRemainder

namespace OAI

/-! The two negative leading terms dominate the complete arithmetic tail,
fixing the sign of the actual theta normalization. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaArithmeticAxisDerivative_split :
    cubicThetaArithmeticAxisDerivative 1=
      (cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 lambdaE+
       cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 (-lambdaE))+
      ∑' n,cubicThetaDerivativeRemainder n := by
  let f := cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1
  have hne : lambdaE≠ -lambdaE := by
    intro h
    have hz : (2:Eisenstein)*lambdaE=0 := by linear_combination h
    rcases mul_eq_zero.mp hz with hz | hz
    · norm_num at hz
    · exact lambdaE_prime.ne_zero hz
  have hp : HasSum (fun n : Eisenstein => if n=lambdaE then f lambdaE else 0) (f lambdaE) :=
    hasSum_ite_eq lambdaE _
  have hn : HasSum (fun n : Eisenstein => if n= -lambdaE then f (-lambdaE) else 0) (f (-lambdaE)) :=
    hasSum_ite_eq (-lambdaE) _
  have h : HasSum f ((f lambdaE+f (-lambdaE))+∑' n,cubicThetaDerivativeRemainder n) := by
    convert (hp.add hn).add cubicThetaDerivativeRemainder_mass.1.hasSum using 1
    funext n
    by_cases h1 : n=lambdaE
    · subst n
      simp only [ite_true,cubicThetaDerivativeRemainder,true_or,
        add_zero]
      simp [hne]
    · by_cases h2 : n= -lambdaE
      · subst n
        simp [h1,cubicThetaDerivativeRemainder]
      · simp [h1,h2,cubicThetaDerivativeRemainder,f]
  exact h.tsum_eq

lemma cubicThetaArithmeticAxisDerivative_re_neg :
    (cubicThetaArithmeticAxisDerivative 1).re<0 := by
  have ht : ‖∑' n,cubicThetaDerivativeRemainder n‖<5/2 :=
    (tsum_of_norm_bounded cubicThetaRemainderWeight_properties.1.hasSum
      cubicThetaDerivativeRemainder_bound).trans_lt cubicThetaRemainderWeight_properties.2.2
  have hr := Complex.re_le_norm (∑' n,cubicThetaDerivativeRemainder n)
  rw [cubicThetaArithmeticAxisDerivative_split,Complex.add_re]
  linarith [cubicThetaFirstPair_real_bound]

theorem cubicThetaArithmeticBaseScalar_eq_one : cubicThetaArithmeticBaseScalar=1 :=
  cubicThetaArithmeticBaseScalar_eq_one_of_axisDerivative_neg
    cubicThetaArithmeticAxisDerivative_re_neg

end CubicFirstMoment

end

end OAI
