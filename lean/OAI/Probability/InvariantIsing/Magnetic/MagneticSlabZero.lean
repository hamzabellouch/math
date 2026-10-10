import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabCoefficient

namespace OAI

/-! Relative derivative bounds for the ordinary Gaussian root step.
No positive cascade exponent is needed at this level. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticScalarSlabJet_zero_third_relative (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (v z : ℝ) :
    |(magneticScalarSlabJet L hL 0 v).second z| ≤
      magneticThirdRatioCap L * (magneticScalarSlabJet L hL 0 v).first z := by
  let P := magneticLogCoshMeanJet L hL
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have htan : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hM : ∀ z, |P.value z| ≤ 1 :=
    (fieldScalarMean_regular L hL measurable_logCosh logCosh_linearGrowth
      htan field_abs_tanh_le_one).2
  obtain ⟨B, _, bQ⟩ := P.bFirst
  have hQ : ∀ z, 0 ≤ P.first z := fun z => (fieldScalarLogCoshSecond_pos L hL z).le
  have hR : ∀ z, |P.second z| ≤ magneticThirdRatioCap L * P.first z :=
    fieldScalarLogCoshThird_relative L hL
  have he := fieldThirdTransform_relative_bound (le_refl (0 : ℝ)) (Real.toNNReal v)
    hF.1 hF.2 P.mValue P.mFirst P.mSecond hM bQ hQ
    (magneticThirdRatioCap_nonneg L) hR z
  simpa only [magneticScalarSlabJet, MagneticContinuationJet.transition, P,
    magneticContinuationSecond, fieldThirdTransform, fieldCurvatureTransform,
    fieldTiltSpatial, zero_mul, mul_zero, add_zero] using he

lemma magneticScalarSlabJet_zero_fourth_relative (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1) (v z : ℝ) :
    |(magneticScalarSlabJet L hL 0 v).third z| ≤
      magneticFourthRatioCap L * (magneticScalarSlabJet L hL 0 v).first z := by
  let P := magneticLogCoshMeanJet L hL
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have htan : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hM : ∀ z, |P.value z| ≤ 1 :=
    (fieldScalarMean_regular L hL measurable_logCosh logCosh_linearGrowth
      htan field_abs_tanh_le_one).2
  have hQ : ∀ z, 0 ≤ P.first z := fun z => (fieldScalarLogCoshSecond_pos L hL z).le
  have hQ1 : ∀ z, P.first z ≤ 1 := by
    intro z
    have hh := fieldScalarLogCoshSecond_le_spin_variance L hL hL1 z
    change P.first z ≤ 1 - (P.value z) ^ 2 at hh
    linarith [sq_nonneg (P.value z)]
  have hR : ∀ z, |P.second z| ≤ magneticThirdRatioCap L * P.first z :=
    fieldScalarLogCoshThird_relative L hL
  have hS : ∀ z, |P.third z| ≤ magneticFourthRatioCap L * P.first z :=
    fieldScalarLogCoshFourth_relative L hL hL1
  have he := fieldFourthTransform_relative_bound (le_refl (0 : ℝ)) (Real.toNNReal v)
    hF.1 hF.2 P.mValue P.mFirst P.mSecond P.mThird hM hQ hQ1
    (magneticThirdRatioCap_nonneg L) (magneticFourthRatioCap_nonneg L) hR hS z
  simpa only [magneticScalarSlabJet, MagneticContinuationJet.transition, P,
    magneticContinuationThird, magneticContinuationSecond, fieldFourthTransform,
    fieldThirdTransform, fieldCurvatureTransform, fieldTiltSpatial,
    zero_mul, mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0)] using he

lemma magneticScalarInverse_zero_weighted_second_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1) (v s : ℝ) :
    |magneticScalarInverseCurvature L hL 0 v s * magneticScalarInverseSecond L hL 0 v s| ≤
      magneticSlabPotentialCap L 0 := by
  let b := magneticScalarSlabBias L 0 v s
  let J := magneticScalarSlabJet L hL 0 v
  have hq : 0 < J.first b := magneticScalarSlabJet_curvature_pos L hL (le_refl _) v b
  have hrq : |J.second b / J.first b| ≤ magneticThirdRatioCap L := by
    rw [abs_div, abs_of_pos hq]
    exact (div_le_iff₀ hq).mpr (magneticScalarSlabJet_zero_third_relative L hL v b)
  have hdq : |J.third b / J.first b| ≤ magneticFourthRatioCap L := by
    rw [abs_div, abs_of_pos hq]
    exact (div_le_iff₀ hq).mpr (magneticScalarSlabJet_zero_fourth_relative L hL hL1 v b)
  have he : magneticScalarInverseCurvature L hL 0 v s * magneticScalarInverseSecond L hL 0 v s =
      J.third b / J.first b - (J.second b / J.first b) ^ 2 := by
    rw [magneticScalarInverseCurvature_eq_jet]
    dsimp only [magneticScalarInverseSecond, J, b]
    field_simp [hq.ne']
  rw [he]
  have hr2 : |(J.second b / J.first b) ^ 2| ≤ (magneticThirdRatioCap L) ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hrq 2
  have hh := (abs_sub _ _).trans (add_le_add hdq hr2)
  simpa only [magneticSlabPotentialCap, magneticFourthRatioCap, magneticThirdRatioCap,
    abs_zero, mul_zero, zero_mul, add_zero, zero_pow (by norm_num : 2 ≠ 0)] using hh

end InvariantIsing

end

end OAI
