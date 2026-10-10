import OAI.Probability.InvariantIsing.Magnetic.MagneticGaussianLaplace
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-! Positive-variance scalar Gaussian transitions are smooth in the
spatial coordinate even when the bounded terminal test has no derivatives.
This justifies the interior fourth derivatives in the inverse-mean
parabolic comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma analyticAt_fieldSpinTransition_nonneg {F A : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hA : Measurable A)
    {K : ℝ} (bA : ∀ y, |A y| ≤ K) (hA0 : ∀ y, 0 ≤ A y)
    (ζ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (z : ℝ) :
    AnalyticAt ℝ (fieldSpinTransition ζ v F A) z := by
  have hn := magneticGaussian_weighted_analytic hF hG hA bA hA0 ζ v hv z
  have hd := magneticGaussian_weighted_analytic hF hG measurable_const
    (show ∀ y : ℝ, |(1 : ℝ)| ≤ 1 from fun _ => by norm_num)
    (show ∀ _ : ℝ, (0 : ℝ) ≤ 1 from fun _ => zero_le_one) ζ v hv z
  simp only [mul_one] at hd
  have hp : 0 < ∫ y, Real.exp (ζ * F y) ∂gaussianReal z v := by
    apply IsingPerceptron.integral_exp_pos
    exact integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG ζ
  have he : fieldSpinTransition ζ v F A = fun x =>
      (∫ y, Real.exp (ζ * F y) * A y ∂gaussianReal x v) /
        (∫ y, Real.exp (ζ * F y) ∂gaussianReal x v) := by
    funext x
    exact integral_tilted_eq_div (gaussianReal x v) (fun y => ζ * F y) A
  rw [he]
  exact hn.div hd hp.ne'

lemma analyticAt_fieldSpinTransition {F A : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hA : Measurable A)
    {K : ℝ} (bA : ∀ y, |A y| ≤ K)
    (ζ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (z : ℝ) :
    AnalyticAt ℝ (fieldSpinTransition ζ v F A) z := by
  have hK : 0 ≤ K := (abs_nonneg (A 0)).trans (bA 0)
  have hB : ∀ y, |A y + K| ≤ 2 * K := by
    intro y
    exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hK]; linarith [bA y])
  have hB0 : ∀ y, 0 ≤ A y + K := by
    intro y
    linarith [(abs_le.mp (bA y)).1]
  have ha := analyticAt_fieldSpinTransition_nonneg hF hG (hA.add_const K) hB hB0 ζ v hv z
  have he : (fun x => fieldSpinTransition ζ v F (fun y => A y + K) x - K) =
      fieldSpinTransition ζ v F A := by
    funext x
    rw [fieldSpinTransition_add ζ v hF hG hA measurable_const bA
      (fun _ => (abs_of_nonneg hK).le), fieldSpinTransition_const ζ v hF hG]
    ring
  rw [← he]
  exact ha.sub analyticAt_const

lemma contDiff_fieldSpinTransition {F A : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hA : Measurable A)
    {K : ℝ} (bA : ∀ y, |A y| ≤ K)
    (ζ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fieldSpinTransition ζ v F A) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (analyticAt_fieldSpinTransition hF hG hA bA ζ v hv z).contDiffAt

end InvariantIsing

end

end OAI
