import OAI.Probability.InvariantIsing.Fields.FieldScalarLogCoshSecond

namespace OAI

/-! Third spatial differentiation of one actual Gaussian backward step.
The formula is kept as tilted averages, so it also applies to zero variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldCurvatureTransform (ζ : ℝ) (v : ℝ≥0) (F M Q : ℝ → ℝ) (z : ℝ) : ℝ :=
  fieldSpinTransition ζ v F Q z + ζ *
    (fieldSpinTransition ζ v F (fun y => (M y) ^ 2) z -
      (fieldSpinTransition ζ v F M z) ^ 2)

def fieldThirdTransform (ζ : ℝ) (v : ℝ≥0) (F M Q R : ℝ → ℝ) (z : ℝ) : ℝ :=
  (fieldSpinTransition ζ v F R z + ζ *
    (fieldSpinTransition ζ v F (fun y => Q y * M y) z -
      fieldSpinTransition ζ v F Q z * fieldSpinTransition ζ v F M z)) +
  ζ * ((fieldSpinTransition ζ v F (fun y => 2 * M y * Q y) z + ζ *
    (fieldSpinTransition ζ v F (fun y => (M y) ^ 2 * M y) z -
      fieldSpinTransition ζ v F (fun y => (M y) ^ 2) z *
        fieldSpinTransition ζ v F M z)) -
    2 * fieldSpinTransition ζ v F M z * fieldCurvatureTransform ζ v F M Q z)

lemma hasDerivAt_fieldCurvatureTransform (ζ : ℝ) (v : ℝ≥0)
    {F M Q R : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q) (hR : Measurable R)
    {K C D : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ C) (bR : ∀ y, |R y| ≤ D)
    (dF : ∀ y, HasDerivAt F (M y) y)
    (dM : ∀ y, HasDerivAt M (Q y) y)
    (dQ : ∀ y, HasDerivAt Q (R y) y) (z : ℝ) :
    HasDerivAt (fieldCurvatureTransform ζ v F M Q)
      (fieldThirdTransform ζ v F M Q R z) z := by
  have hm2 : Measurable (fun y => (M y) ^ 2) := hM.pow_const 2
  have hmQ : Measurable (fun y => 2 * M y * Q y) :=
    (measurable_const.mul hM).mul hQ
  have bm2 : ∀ y, |(M y) ^ 2| ≤ K ^ 2 := by
    intro y
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (bM y) 2
  have bmQ : ∀ y, |2 * M y * Q y| ≤ 2 * K * C := by
    intro y
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (bM y) (by norm_num)) (bQ y)
      (abs_nonneg _) (by positivity)
  have dm2 : ∀ y, HasDerivAt (fun w => (M w) ^ 2) (2 * M y * Q y) y := by
    intro y
    convert (dM y).pow 2 using 1
    norm_num
  have hmean := hasDerivAt_fieldSpinTransition ζ v hF hG hM hM hQ
    hK hK bM bM bQ dF dM z
  have hmean' : HasDerivAt (fieldSpinTransition ζ v F M)
      (fieldCurvatureTransform ζ v F M Q z) z := by
    simpa only [fieldCurvatureTransform, pow_two] using hmean
  have hsecond := hasDerivAt_fieldSpinTransition ζ v hF hG hM hQ hR
    hK hC bM bQ bR dF dQ z
  have hsq := hasDerivAt_fieldSpinTransition ζ v hF hG hM hm2 hmQ
    hK (sq_nonneg K) bM bm2 bmQ dF dm2 z
  have hd := hsecond.add ((hsq.sub (hmean'.pow 2)).const_mul ζ)
  convert hd using 1
  · rfl
  · simp [fieldThirdTransform]

lemma measurable_fieldThirdTransform (ζ : ℝ) (v : ℝ≥0)
    {F M Q R : ℝ → ℝ} (hF : Measurable F) (hM : Measurable M)
    (hQ : Measurable Q) (hR : Measurable R) :
    Measurable (fieldThirdTransform ζ v F M Q R) := by
  have hm := measurable_fieldSpinTransition ζ v hF hM
  have hq := measurable_fieldSpinTransition ζ v hF hQ
  have hr := measurable_fieldSpinTransition ζ v hF hR
  have hqm := measurable_fieldSpinTransition ζ v hF (hQ.mul hM)
  have hm2 := measurable_fieldSpinTransition ζ v hF (hM.pow_const 2)
  have hm2m := measurable_fieldSpinTransition ζ v hF ((hM.pow_const 2).mul hM)
  have h2mq : Measurable (fieldSpinTransition ζ v F (fun y => 2 * M y * Q y)) :=
    measurable_fieldSpinTransition ζ v hF ((measurable_const.mul hM).mul hQ)
  exact (hr.add ((hqm.sub (hq.mul hm)).const_mul ζ)).add
    (((h2mq.add ((hm2m.sub (hm2.mul hm)).const_mul ζ)).sub
      ((measurable_const.mul hm).mul
        (hq.add ((hm2.sub (hm.pow_const 2)).const_mul ζ)))).const_mul ζ)

def fieldThirdTransformCap (ζ K C D : ℝ) : ℝ :=
  (D + 2 * |ζ| * C * K) + |ζ| *
    ((2 * K * C + 2 * |ζ| * K ^ 2 * K) + 2 * K * (C + 2 * |ζ| * K ^ 2))

lemma fieldThirdTransform_bound (ζ : ℝ) (v : ℝ≥0)
    {F M Q R : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    {K C D : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ C) (bR : ∀ y, |R y| ≤ D)
    (z : ℝ) : |fieldThirdTransform ζ v F M Q R z| ≤ fieldThirdTransformCap ζ K C D := by
  have bm2 : ∀ y, |(M y) ^ 2| ≤ K ^ 2 := by
    intro y
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (bM y) 2
  have bmQ : ∀ y, |2 * M y * Q y| ≤ 2 * K * C := by
    intro y
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (bM y) (by norm_num)) (bQ y)
      (abs_nonneg _) (by positivity)
  have hfirst := fieldSpinTransition_derivative_bound ζ v hF hG hK hC bM bQ bR z
  have hsecond := fieldSpinTransition_derivative_bound ζ v hF hG hK (sq_nonneg K)
    bM bm2 bmQ z
  have hm := fieldSpinTransition_bound ζ v hF hG bM z
  have hq : |fieldCurvatureTransform ζ v F M Q z| ≤ C + 2 * |ζ| * K ^ 2 := by
    have hh := fieldSpinTransition_derivative_bound ζ v hF hG hK hK bM bM bQ z
    simpa only [fieldCurvatureTransform, pow_two, mul_assoc] using hh
  have hprod : |2 * fieldSpinTransition ζ v F M z * fieldCurvatureTransform ζ v F M Q z| ≤
      2 * K * (C + 2 * |ζ| * K ^ 2) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num)) hq
      (abs_nonneg _) (by positivity)
  unfold fieldThirdTransform fieldThirdTransformCap
  refine (abs_add_le _ _).trans (add_le_add hfirst ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hsecond hprod))
    (abs_nonneg ζ)

end InvariantIsing

end

end OAI
