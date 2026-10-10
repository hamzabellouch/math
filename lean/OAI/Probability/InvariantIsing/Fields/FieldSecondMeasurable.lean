import OAI.Probability.InvariantIsing.Fields.FieldSecondTangentDerivative

namespace OAI

/-! Measurability of the explicit second derivatives of the scalar
Gaussian recursion, including their affine Gaussian weights. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma FieldSmoothFamily.measurable_affine_average {I : Set ℝ} (F : FieldSmoothFamily I)
    (a v ζ : ℝ) {A : (ℝ × ℝ) → ℝ → ℝ}
    (hA : Measurable (fun p : (ℝ × ℝ) × ℝ => A p.1 p.2)) :
    Measurable (fun p => ∫ u, A p u ∂F.affineLaw a v ζ p) := by
  have hU : Measurable (fun p : (ℝ × ℝ) × ℝ => F.affineShift a v p.1 p.2) :=
    F.mU.comp (by fun_prop)
  simp only [FieldSmoothFamily.affineLaw, integral_tilted_eq_div]
  exact ((hU.const_mul ζ).exp.mul hA).stronglyMeasurable.integral_prod_right'.measurable.div
    ((hU.const_mul ζ).exp.stronglyMeasurable.integral_prod_right'.measurable)

namespace FieldSecondFamily

variable {I : Set ℝ} (F : FieldSecondFamily I)

lemma joint_measurable_shiftedMean (a v : ℝ) :
    Measurable (fun p : (ℝ × ℝ) × ℝ => F.shiftedMean a v p.2 p.1) :=
  F.mX.comp (by fun_prop)

lemma joint_measurable_shiftedTangent (a v : ℝ) :
    Measurable (fun p : (ℝ × ℝ) × ℝ => F.shiftedTangent a v p.2 p.1) := by
  exact (F.mT.comp (by fun_prop)).add ((F.mX.comp (by fun_prop)).mul (by
    dsimp only [fieldAmplitudeSlope]
    fun_prop))

lemma joint_measurable_shiftedMixed (a v : ℝ) :
    Measurable (fun p : (ℝ × ℝ) × ℝ => F.shiftedMixed a v p.2 p.1) := by
  exact (F.mTX.comp (by fun_prop)).add ((F.mXX.comp (by fun_prop)).mul (by
    dsimp only [fieldAmplitudeSlope]
    fun_prop))

lemma joint_measurable_shiftedSecond (a v : ℝ) :
    Measurable (fun p : (ℝ × ℝ) × ℝ => F.shiftedSecond a v p.2 p.1) := by
  exact (((F.mTT.comp (by fun_prop)).add
    (((F.mTX.comp (by fun_prop)).const_mul 2).mul (by
      dsimp only [fieldAmplitudeSlope]; fun_prop))).add
    ((F.mXX.comp (by fun_prop)).mul (by
      dsimp only [fieldAmplitudeSlope]; fun_prop))).add
    ((F.mX.comp (by fun_prop)).mul (by
      dsimp only [fieldAmplitudeCurvature, fieldAmplitudeSlope]; fun_prop))

lemma measurable_mixedMean (a v ζ : ℝ) : Measurable (F.mixedMean a v ζ) := by
  exact (F.toFieldSmoothFamily.measurable_affine_average a v ζ
    (F.joint_measurable_shiftedMixed a v)).add
    (((F.toFieldSmoothFamily.measurable_affine_average a v ζ
      ((F.joint_measurable_shiftedMean a v).mul (F.joint_measurable_shiftedTangent a v))).sub
      ((F.measurable_mean a v ζ).mul (F.toFieldSmoothFamily.measurable_affine_average a v ζ
        (F.joint_measurable_shiftedTangent a v)))).const_mul ζ)

lemma measurable_secondMean (a v ζ : ℝ) : Measurable (F.secondMean a v ζ) := by
  exact (F.toFieldSmoothFamily.measurable_affine_average a v ζ
    (F.joint_measurable_shiftedSecond a v)).add
    (((F.toFieldSmoothFamily.measurable_affine_average a v ζ
      ((F.joint_measurable_shiftedTangent a v).pow_const 2)).sub
      ((F.toFieldSmoothFamily.measurable_affine_average a v ζ
        (F.joint_measurable_shiftedTangent a v)).pow_const 2)).const_mul ζ)

end FieldSecondFamily
end InvariantIsing

end

end OAI
