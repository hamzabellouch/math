import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDerivativeTailBounds
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFirstPair

namespace OAI

/-! Absolute vertical-term estimates at the two arithmetic lattice scales. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_lambda_mul (m : Eisenstein) :
    ‖cubicThetaFrequency (lambdaE*m)‖=Real.sqrt 3*Real.sqrt (norm m)/9 := by
  simpa using cubicThetaFrequency_primary_norm m 1

lemma cubicThetaFrequency_lambda_cube_mul (m : Eisenstein) :
    ‖cubicThetaFrequency (lambdaE^3*m)‖=Real.sqrt 3*Real.sqrt (norm m)/3 := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (by positivity)).mp
  rw [cubicThetaFrequency_sq]
  have he : norm (lambdaE^3*m)=27*norm m := by
    change Complex.normSq (((lambdaE^3*m:Eisenstein):ℂ))=_
    simp only [Subalgebra.coe_mul,Subalgebra.coe_pow,Complex.normSq_mul,
      map_pow,lambdaE_coe,traceLambda_normSq]
    unfold norm
    ring
  rw [he,div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3),
    Real.sq_sqrt (norm_nonneg m)]
  ring

lemma cubicThetaSeriesTermVertical_axis_norm {a : Eisenstein → ℂ} {n : Eisenstein}
    (hn : n≠0) :
    ‖cubicThetaSeriesTermVertical a 0 1 n‖=
      ‖a n‖*‖cubicThetaFrequency n‖*‖cubicThetaWhittakerDerivative ‖cubicThetaFrequency n‖‖ := by
  simp only [cubicThetaSeriesTermVertical,hn,ite_false,mul_one,norm_mul,Circle.norm_coe,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)]
  ring

lemma cubicThetaSeriesTermVertical_primary_bound {n m : Eisenstein}
    (hn : n≠0) (hN : 4≤norm m)
    (he : n=lambdaE*m ∨ n= -lambdaE*m)
    (hc : ‖cubicThetaArithmeticCoefficient n‖≤81/2) :
    ‖cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 n‖≤
      (9/2:ℝ)*Real.pi*(norm m*Real.exp (-(241/100:ℝ)*Real.sqrt (norm m))) := by
  have hf : ‖cubicThetaFrequency n‖=Real.sqrt 3*Real.sqrt (norm m)/9 := by
    rcases he with rfl | rfl
    · exact cubicThetaFrequency_lambda_mul m
    · rw [neg_mul,cubicThetaFrequency_neg_norm,cubicThetaFrequency_lambda_mul]
  rw [cubicThetaSeriesTermVertical_axis_norm hn,hf]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity))
    (_root_.norm_nonneg _)).trans (cubicThetaPrimary_derivative_tail hN)

lemma cubicThetaSeriesTermVertical_ramified_bound {n m : Eisenstein}
    (hn : n≠0) (hm : m≠0) (he : n=lambdaE^3*m)
    (hc : ‖cubicThetaArithmeticCoefficient n‖≤27) :
    ‖cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 n‖≤
      27*Real.pi*(norm m*Real.exp (-(29/4:ℝ)*Real.sqrt (norm m))) := by
  rw [cubicThetaSeriesTermVertical_axis_norm hn,he,cubicThetaFrequency_lambda_cube_mul]
  rw [he] at hc
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity))
    (_root_.norm_nonneg _)).trans (cubicThetaRamified_derivative_tail (one_le_norm hm))

end CubicFirstMoment

end

end OAI
