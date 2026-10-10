import OAI.Geometry.CylinderCovering.Rational.DictionaryCostDefinitions
import OAI.Geometry.CylinderCovering.Rational.CoordinateDictionary
import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory
namespace RationalDictionary.CostTransfer

lemma orthonormalWeight_eq_weight (d0 k : ℝ) (p : Plane) :
    orthonormalWeight d0 k p = RuledApproximation.weight (k • velocity d0 p) := by
  unfold orthonormalWeight RuledApproximation.weight
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, PiLp.smul_apply, smul_eq_mul, velocity, vec2, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 2
  ring

lemma uncenteredDomain_measurable (d0 eta0 k : ℝ) :
    MeasurableSet (uncenteredDomain d0 eta0 k) := by
  have h1 : MeasurableSet {p : Plane | 0 ≤ p 1} :=
    measurableSet_le measurable_const (by fun_prop)
  have h2 : MeasurableSet {p : Plane | p 1 ≤ 3 / 2} :=
    measurableSet_le (by fun_prop) measurable_const
  have h3 : MeasurableSet {p : Plane | |p 0| ≤ c0 * p 1} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have h4 : MeasurableSet {p : Plane | p 1 ≤ 1 + k ^ 2 * (a0 d0 (p 0) + eta0)} := by
    unfold a0 A0 B0
    exact measurableSet_le (by fun_prop) (by fun_prop)
  exact h1.inter (h2.inter (h3.inter h4))

lemma labelMap_injective : Function.Injective labelMap := by
  exact Function.LeftInverse.injective inverseLabelMap_labelMap

lemma labelMap_domain {d0 : ℝ} (hd : 0 < d0) (eta0 k : ℝ) :
    labelMap '' uncenteredDomain d0 eta0 k =
      SlopeRational.labelDomain (centeredRegularization d0)
        (centeredTilt d0 k) (centeredPadding eta0 k) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (labelDomain_iff hd eta0 k q).mp hq
  · intro hp
    refine ⟨inverseLabelMap p, ?_, labelMap_inverseLabelMap p⟩
    apply (labelDomain_iff hd eta0 k _).mpr
    simpa only [labelMap_inverseLabelMap] using hp

lemma labelMap_deriv (p : Plane) :
    HasFDerivAt labelMap (RuledApproximation.matrixCLM ell 0 0 (-(1 / 2))) p := by
  have heq : labelMap = fun z : Plane =>
      RuledApproximation.matrixCLM ell 0 0 (-(1 / 2)) z + vec2 0 (1 / 2) := by
    funext z
    ext i
    fin_cases i <;> simp [labelMap, RuledApproximation.matrixCLM_apply,
      RuledApproximation.vec2, vec2]
    ring
  rw [heq]
  exact (RuledApproximation.matrixCLM ell 0 0 (-(1 / 2))).hasFDerivAt.add_const _

lemma labelMap_abs_det :
    |(RuledApproximation.matrixCLM ell 0 0 (-(1 / 2))).det| = ell / 2 := by
  rw [ContinuousLinearMap.det, RuledApproximation.matrixCLM_det]
  have he : ell * (-(1 / 2 : ℝ)) - 0 * 0 = -(ell / 2) := by ring
  rw [he, abs_neg, abs_of_pos (div_pos ell_pos (by norm_num))]

lemma labelMap_integral (S : Set Plane) (hS : MeasurableSet S) (f : Plane → ℝ) :
    (∫ p in labelMap '' S, f p) = (ell / 2) * ∫ p in S, f (labelMap p) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun p _ => (labelMap_deriv p).hasFDerivWithinAt) labelMap_injective.injOn f]
  simp only [labelMap_abs_det, smul_eq_mul]
  exact integral_const_mul _ _

lemma weight_dictionary {d0 : ℝ} (hd : 0 < d0) {eta0 k : ℝ}
    {p : Plane} (hp : p ∈ uncenteredDomain d0 eta0 k) :
    RuledApproximation.physicalWeight SlopeRational.physicalScale
      (centeredTilt d0 k • SlopeRational.field (centeredRegularization d0) (labelMap p)) =
      orthonormalWeight d0 k p := by
  have hs : p 1 + d0 ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hp.1 hd)
  have h := squared_slope_dictionary hs k (p 0)
  have he :
      (centeredTilt d0 k * SlopeRational.a (d0 / 2) (ell * p 0) ((1 - p 1) / 2)) ^ 2 +
        c0 ^ 2 * (centeredTilt d0 k *
          SlopeRational.b (d0 / 2) (ell * p 0) ((1 - p 1) / 2)) ^ 2 =
      k ^ 2 * (v1 d0 (p 0) (p 1) ^ 2 + v2 d0 (p 0) (p 1) ^ 2) := by
    nlinarith only [h]
  change 1 / Real.sqrt
    (1 + (centeredTilt d0 k * SlopeRational.a (d0 / 2) (ell * p 0) ((1 - p 1) / 2)) ^ 2 +
      c0 ^ 2 * (centeredTilt d0 k *
        SlopeRational.b (d0 / 2) (ell * p 0) ((1 - p 1) / 2)) ^ 2) = _
  simpa only [add_assoc, orthonormalWeight] using congrArg (fun z : ℝ => 1 / Real.sqrt (1 + z)) he

theorem weightedCost_dictionary {d0 : ℝ} (hd : 0 < d0) (eta0 k : ℝ) :
    SlopeRational.weightedCost (centeredRegularization d0) (centeredTilt d0 k)
      (centeredPadding eta0 k) = orthonormalCost d0 eta0 k / 8 := by
  unfold SlopeRational.weightedCost orthonormalCost
  rw [← labelMap_domain hd eta0 k]
  rw [labelMap_integral _ (uncenteredDomain_measurable d0 eta0 k)]
  have hi :
      (∫ p in uncenteredDomain d0 eta0 k,
        RuledApproximation.physicalWeight SlopeRational.physicalScale
          (centeredTilt d0 k • SlopeRational.field (centeredRegularization d0) (labelMap p))) =
      ∫ p in uncenteredDomain d0 eta0 k, orthonormalWeight d0 k p := by
    apply setIntegral_congr_fun (uncenteredDomain_measurable d0 eta0 k)
    intro p hp
    exact weight_dictionary hd hp
  rw [hi]
  have hc : SlopeRational.physicalScale * (ell / 2) = 1 / 8 := by
    change c0 * (ell / 2) = 1 / 8
    nlinarith [ell_mul_c0]
  rw [← mul_assoc, hc]
  ring

theorem cost_dictionary : CostDictionaryStatement := by
  intro d0 hd eta0 k
  exact weightedCost_dictionary hd eta0 k

end RationalDictionary.CostTransfer

end

end OAI
