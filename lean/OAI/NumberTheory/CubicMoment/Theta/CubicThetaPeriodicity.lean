import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFunction

namespace OAI

/-! Exact translation periods on the common cubic cusp frequency lattice. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_period_phase (n m : Eisenstein) :
    (Real.fourierChar (tracePair (cubicThetaFrequency n) ((lambdaE^3*m:Eisenstein):ℂ)):ℂ) = 1 := by
  have he : tracePair (cubicThetaFrequency n) ((lambdaE^3*m:Eisenstein):ℂ) =
      tracePair ((n*m:Eisenstein):ℂ) (1/traceLambda) := by
    unfold tracePair cubicThetaFrequency
    congr 2
    push_cast
    rw [lambdaE_coe]
    field_simp
  rw [he,tracePhase_div_lambda_one]

lemma cubicThetaSeriesTerm_periodic (a : Eisenstein → ℂ) (m n : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaSeriesTerm a (z+((lambdaE^3*m:Eisenstein):ℂ)) v n =
      cubicThetaSeriesTerm a z v n := by
  by_cases hn : n = 0
  · simp [cubicThetaSeriesTerm,hn]
  · simp only [cubicThetaSeriesTerm,hn,ite_false]
    have he : tracePair (cubicThetaFrequency n) (z+((lambdaE^3*m:Eisenstein):ℂ)) =
        tracePair (cubicThetaFrequency n) z+
          tracePair (cubicThetaFrequency n) ((lambdaE^3*m:Eisenstein):ℂ) := by
      unfold tracePair
      simp only [mul_add,Complex.add_re,mul_add]
    rw [he,AddChar.map_add_eq_mul,Circle.coe_mul,cubicThetaFrequency_period_phase,mul_one]

lemma cubicThetaNonconstant_periodic (a : Eisenstein → ℂ) (m : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaNonconstant a (z+((lambdaE^3*m:Eisenstein):ℂ),v) = cubicThetaNonconstant a (z,v) := by
  unfold cubicThetaNonconstant
  apply tsum_congr
  intro n
  exact cubicThetaSeriesTerm_periodic a m n z v

/-- These translation identities are proved from the arithmetic frequency
lattice, independently of the remaining inversion transformation. -/
theorem cubicThetaFunction_periodic (m : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaFunction (z+((lambdaE^3*m:Eisenstein):ℂ),v) = cubicThetaFunction (z,v) := by
  unfold cubicThetaFunction cubicThetaAuxiliarySeries
  rw [cubicThetaNonconstant_periodic]

end CubicFirstMoment

end

end OAI
