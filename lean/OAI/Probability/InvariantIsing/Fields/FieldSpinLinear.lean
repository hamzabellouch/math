import OAI.Probability.InvariantIsing.Fields.FieldSpinSecondDerivative

namespace OAI

/-! Linear identities for the actual tilted scalar transition. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_const_mul (ζ : ℝ) (v : ℝ≥0) (F a : ℝ → ℝ)
    (c z : ℝ) :
    fieldSpinTransition ζ v F (fun u => c * a u) z = c * fieldSpinTransition ζ v F a z := by
  exact integral_const_mul c _

lemma fieldSpinTransition_add (ζ : ℝ) (v : ℝ≥0) {F a b : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (ha : Measurable a) (hb : Measurable b)
    {A B : ℝ} (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (z : ℝ) :
    fieldSpinTransition ζ v F (fun u => a u + b u) z =
      fieldSpinTransition ζ v F a z + fieldSpinTransition ζ v F b z := by
  have he := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hg ζ
  have : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    MeasureTheory.isProbabilityMeasure_tilted he
  exact integral_add
    (Integrable.of_bound ha.aestronglyMeasurable A
      (Filter.Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using haB u))
    (Integrable.of_bound hb.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using hbB u))

lemma fieldSpinTransition_const (ζ : ℝ) (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (c z : ℝ) :
    fieldSpinTransition ζ v F (fun _ => c) z = c := by
  have he := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hg ζ
  have : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    MeasureTheory.isProbabilityMeasure_tilted he
  simp only [fieldSpinTransition, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]

lemma fieldSpinTransition_generator_difference (ζ η : ℝ) (v : ℝ≥0)
    {F D DD : ℝ → ℝ} (hF : Measurable F) (hg : HasLinearGrowth F)
    (hD : Measurable D) (hDD : Measurable DD)
    {K C : ℝ} (hDb : ∀ u, |D u| ≤ K) (hDDb : ∀ u, |DD u| ≤ C) (z : ℝ) :
    -(fieldSpinTransition ζ v F (fun u => DD u + η * (D u) ^ 2) z) / 2 +
        fieldSpinTransition ζ v F (fun u => DD u + ζ * (D u) ^ 2) z / 2 =
      (ζ - η) / 2 * fieldSpinTransition ζ v F (fun u => (D u) ^ 2) z := by
  have hs : ∀ u, |(D u) ^ 2| ≤ K ^ 2 := fun u => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hDb u) 2
  have hm (r : ℝ) : Measurable (fun u => r * (D u) ^ 2) := (hD.pow_const 2).const_mul r
  have hb (r : ℝ) : ∀ u, |r * (D u) ^ 2| ≤ |r| * K ^ 2 := fun u => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hs u) (abs_nonneg r)
  rw [fieldSpinTransition_add ζ v hF hg hDD (hm η) hDDb (hb η),
    fieldSpinTransition_add ζ v hF hg hDD (hm ζ) hDDb (hb ζ),
    fieldSpinTransition_const_mul, fieldSpinTransition_const_mul]
  ring

end InvariantIsing

end

end OAI
