import OAI.Probability.InvariantIsing.Fields.FieldGaussianFamilyLocal

namespace OAI

/-! Real-variance notation for the scalar recursion. Outside the
positive variance cone the existing Gaussian transform uses zero noise;
these spatial identities remain valid there as well. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma field_sqrt_toNNReal (s : ℝ) :
    Real.sqrt (Real.toNNReal s : ℝ) = Real.sqrt s := by
  rw [← Real.coe_sqrt, Real.sqrt]

lemma field_gaussianTransform_eq_operator (s ζ : ℝ) (F : ℝ → ℝ) :
    gaussianTransform s ζ F = gaussianOperator ζ (Real.toNNReal s) F := by
  funext z
  unfold gaussianTransform gaussianOperator
  rw [field_sqrt_toNNReal]
  split_ifs
  · rfl
  · ring

lemma field_gaussianTiltAverage_eq_transition (s ζ : ℝ) {F a : ℝ → ℝ}
    (hF : Measurable F) (ha : Measurable a) :
    gaussianTiltAverage s ζ F a = fieldSpinTransition ζ (Real.toNNReal s) F a := by
  funext z
  rw [fieldSpinTransition_eq_standard ζ (Real.toNNReal s) hF ha]
  unfold gaussianTiltAverage
  rw [field_sqrt_toNNReal]

lemma field_gaussianTiltAverage_bound (s ζ : ℝ) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (ha : Measurable a)
    {K : ℝ} (hK : ∀ y, |a y| ≤ K) (z : ℝ) :
    |gaussianTiltAverage s ζ F a z| ≤ K := by
  rw [field_gaussianTiltAverage_eq_transition s ζ hF ha]
  exact fieldSpinTransition_bound ζ (Real.toNNReal s) hF hG hK z

lemma field_gaussianTransform_hasDerivAt (s ζ : ℝ) {F D : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hD : Measurable D)
    {K : ℝ} (hK : 0 ≤ K) (hDb : ∀ y, |D y| ≤ K)
    (hd : ∀ y, HasDerivAt F (D y) y) (z : ℝ) :
    HasDerivAt (gaussianTransform s ζ F) (gaussianTiltAverage s ζ F D z) z := by
  rw [field_gaussianTransform_eq_operator,
    field_gaussianTiltAverage_eq_transition s ζ hF hD]
  exact hasDerivAt_gaussianOperator ζ (Real.toNNReal s) hF hG hD hK hDb hd z

lemma field_gaussianTiltAverage_hasDerivAt (s ζ : ℝ) {F D a b : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (hD : Measurable D) (ha : Measurable a) (hb : Measurable b)
    {C M L : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hDb : ∀ y, |D y| ≤ C) (hab : ∀ y, |a y| ≤ M) (hbb : ∀ y, |b y| ≤ L)
    (hd : ∀ y, HasDerivAt F (D y) y) (had : ∀ y, HasDerivAt a (b y) y)
    (z : ℝ) :
    HasDerivAt (gaussianTiltAverage s ζ F a)
      (gaussianTiltAverage s ζ F b z + ζ *
        (gaussianTiltAverage s ζ F (fun y => a y * D y) z -
          gaussianTiltAverage s ζ F a z * gaussianTiltAverage s ζ F D z)) z := by
  have hm : Measurable (fun y => a y * D y) := ha.mul hD
  rw [field_gaussianTiltAverage_eq_transition s ζ hF ha,
    field_gaussianTiltAverage_eq_transition s ζ hF hb,
    field_gaussianTiltAverage_eq_transition s ζ hF hm,
    field_gaussianTiltAverage_eq_transition s ζ hF hD]
  exact hasDerivAt_fieldSpinTransition ζ (Real.toNNReal s) hF hG hD ha hb
    hC hM hDb hab hbb hd had z

end InvariantIsing

end

end OAI
