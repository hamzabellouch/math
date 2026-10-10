import OAI.Probability.InvariantIsing.Fields.FieldFiniteMoments

namespace OAI

/-! Measurability of the joint finite-height Gaussian mark data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma measurable_shiftedMean (a : ℝ) (v : Fin n → ℝ) (p : FieldCovariate n) :
    Measurable (fun u => F.shiftedMean a v u p) :=
  F.mX.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)

lemma measurable_shiftedTangent (a : ℝ) (v : Fin n → ℝ) (i : Fin n) (p : FieldCovariate n) :
    Measurable (fun u => F.shiftedTangent a v i u p) := by
  exact ((F.mP i).comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).add
    ((F.mX.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).mul (by fun_prop))

lemma measurable_shiftedMixed (a : ℝ) (v : Fin n → ℝ) (i : Fin n) (p : FieldCovariate n) :
    Measurable (fun u => F.shiftedMixed a v i u p) := by
  exact ((F.mPX i).comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).add
    ((F.mXX.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).mul (by fun_prop))

lemma measurable_shiftedHessian (a : ℝ) (v : Fin n → ℝ) (i j : Fin n)
    (p : FieldCovariate n) : Measurable (fun u => F.shiftedHessian a v i j u p) := by
  have hm : Measurable (fun u : ℝ => F.shiftPoint a v u p) := by
    dsimp only [shiftPoint]
    fun_prop
  exact (((((F.mPP i j).comp hm).add (((F.mPX i).comp hm).mul (by fun_prop))).add
    (((F.mPX j).comp hm).mul (by fun_prop))).add
    ((((F.mXX.comp hm).mul (by fun_prop))).mul (by fun_prop))).add
    ((F.mX.comp hm).mul (by fun_prop))

lemma measurable_affineDifferential (a : ℝ) (v : Fin n → ℝ) (p : FieldCovariate n) :
    Measurable (F.affineDifferential a v p) :=
  measurable_fieldFiniteLinear (fun i => F.measurable_shiftedTangent a v i p)
    (F.measurable_shiftedMean a v p)

lemma measurable_affine_average (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {A : FieldCovariate n → ℝ → ℝ}
    (hA : Measurable (fun p : FieldCovariate n × ℝ => A p.1 p.2)) :
    Measurable (fun p => ∫ u, A p u ∂F.affineLaw a v ζ p) := by
  have hU : Measurable (fun p : FieldCovariate n × ℝ => F.affineShift a v p.1 p.2) :=
    F.mU.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)
  simp only [affineLaw, integral_tilted_eq_div]
  exact ((hU.const_mul ζ).exp.mul hA).stronglyMeasurable.integral_prod_right'.measurable.div
    ((hU.const_mul ζ).exp.stronglyMeasurable.integral_prod_right'.measurable)

lemma joint_measurable_shiftedMean (a : ℝ) (v : Fin n → ℝ) :
    Measurable (fun p : FieldCovariate n × ℝ => F.shiftedMean a v p.2 p.1) :=
  F.mX.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)

lemma joint_measurable_shiftedTangent (a : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    Measurable (fun p : FieldCovariate n × ℝ => F.shiftedTangent a v i p.2 p.1) := by
  exact ((F.mP i).comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).add
    ((F.mX.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).mul (by
      dsimp only [fieldFiniteSlope, fieldFiniteVariance]; fun_prop))

lemma joint_measurable_shiftedMixed (a : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    Measurable (fun p : FieldCovariate n × ℝ => F.shiftedMixed a v i p.2 p.1) := by
  exact ((F.mPX i).comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).add
    ((F.mXX.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).mul (by
      dsimp only [fieldFiniteSlope, fieldFiniteVariance]; fun_prop))

lemma joint_measurable_shiftedHessian (a : ℝ) (v : Fin n → ℝ) (i j : Fin n) :
    Measurable (fun p : FieldCovariate n × ℝ => F.shiftedHessian a v i j p.2 p.1) := by
  have hm : Measurable (fun p : FieldCovariate n × ℝ => F.shiftPoint a v p.2 p.1) := by
    dsimp only [shiftPoint, fieldFiniteVariance]
    fun_prop
  have hs (k : Fin n) : Measurable (fun p : FieldCovariate n × ℝ =>
      fieldFiniteSlope a v p.1.1 k * p.2) := by
    dsimp only [fieldFiniteSlope, fieldFiniteVariance]
    fun_prop
  have hc : Measurable (fun p : FieldCovariate n × ℝ =>
      fieldFiniteCurvature a v p.1.1 i j * p.2) := by
    dsimp only [fieldFiniteCurvature, fieldFiniteSlope, fieldFiniteVariance]
    fun_prop
  exact (((((F.mPP i j).comp hm).add (((F.mPX i).comp hm).mul (hs j))).add
    (((F.mPX j).comp hm).mul (hs i))).add
    (((F.mXX.comp hm).mul (hs i)).mul (hs j))).add ((F.mX.comp hm).mul hc)

end FieldFiniteFamily
end InvariantIsing

end

end OAI
