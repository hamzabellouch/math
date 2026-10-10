import OAI.Probability.InvariantIsing.Fields.FieldGaussianFolding
import OAI.Probability.IsingPerceptron.FieldChain
import OAI.Probability.IsingPerceptron.BoundedTiltAverage

namespace OAI

/-! The folded likelihood comparison for the actual Gaussian tilted
transition, with its integrability discharged by linear growth. -/

noncomputable section
open scoped NNReal
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

private lemma field_test_exp_integrable (v : ℝ≥0) (z ζ : ℝ)
    (F f : ℝ → ℝ) (hF : Measurable F) (hgrowth : HasLinearGrowth F)
    (hf : Measurable f) {C : ℝ} (hbound : ∀ u, |f u| ≤ C) :
    Integrable (fun u => Real.exp (ζ * F u) * f |u|) (gaussianReal z v) := by
  have hw := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v)
    hF hgrowth ζ
  have hi := hw.bdd_mul (hf.comp measurable_abs).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => by simpa only [Function.comp_apply, Real.norm_eq_abs] using hbound |u|))
  simpa only [Function.comp_apply, mul_comm] using hi

/-- Absolute child position is stochastically increasing in a nonnegative
parent position under an arbitrary even linearly growing payoff. -/
theorem field_gaussian_tilt_abs_parent_order (v : ℝ≥0) (hv : v ≠ 0) (ζ : ℝ)
    (F f : ℝ → ℝ) (hF : Measurable F) (hFeven : Function.Even F)
    (hgrowth : HasLinearGrowth F) (hf : Measurable f)
    (hmono : MonotoneOn f (Ici 0)) {C : ℝ} (hbound : ∀ u, |f u| ≤ C)
    {z₀ z₁ : ℝ} (hz₀ : 0 ≤ z₀) (hzz : z₀ ≤ z₁) :
    (∫ u, f |u| ∂(gaussianReal z₀ v).tilted (fun u => ζ * F u)) ≤
      (∫ u, f |u| ∂(gaussianReal z₁ v).tilted (fun u => ζ * F u)) := by
  have hvp : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hw (z : ℝ) : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hgrowth ζ
  rw [integral_tilted_eq_div, integral_tilted_eq_div,
    field_gaussian_folded_ratio v hv z₀ ζ F f hFeven
      (field_test_exp_integrable v z₀ ζ F f hF hgrowth hf hbound) (hw z₀),
    field_gaussian_folded_ratio v hv z₁ ζ F f hFeven
      (field_test_exp_integrable v z₁ ζ F f hF hgrowth hf hbound) (hw z₁)]
  exact fieldFolded_parent_expectation_le hvp ζ F f hf hmono hbound hz₀ hzz
    (fieldFoldedWeight_integrable v hv z₀ ζ F hFeven (hw z₀))
    (fieldFoldedWeight_integrable v hv z₁ ζ F hFeven (hw z₁))
    (fieldFoldedWeight_mass_pos v hv z₀ ζ F hFeven (hw z₀))
    (fieldFoldedWeight_mass_pos v hv z₁ ζ F hFeven (hw z₁))

/-- Adding an even payoff which increases in absolute position raises the
actual absolute-position transition. -/
theorem field_gaussian_tilt_abs_payoff_order (v : ℝ≥0) (hv : v ≠ 0) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (F G f : ℝ → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFeven : Function.Even F) (hGeven : Function.Even G)
    (hFgrowth : HasLinearGrowth F) (hGgrowth : HasLinearGrowth G)
    (hFG : MonotoneOn (fun u => G u - F u) (Ici 0))
    (hf : Measurable f) (hmono : MonotoneOn f (Ici 0))
    {C : ℝ} (hbound : ∀ u, |f u| ≤ C) (z : ℝ) :
    (∫ u, f |u| ∂(gaussianReal z v).tilted (fun u => ζ * F u)) ≤
      (∫ u, f |u| ∂(gaussianReal z v).tilted (fun u => ζ * G u)) := by
  have hwF : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hFgrowth ζ
  have hwG : Integrable (fun u => Real.exp (ζ * G u)) (gaussianReal z v) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hG hGgrowth ζ
  rw [integral_tilted_eq_div, integral_tilted_eq_div,
    field_gaussian_folded_ratio v hv z ζ F f hFeven
      (field_test_exp_integrable v z ζ F f hF hFgrowth hf hbound) hwF,
    field_gaussian_folded_ratio v hv z ζ G f hGeven
      (field_test_exp_integrable v z ζ G f hG hGgrowth hf hbound) hwG]
  exact fieldFolded_payoff_expectation_le v hζ F G f hFG hf hmono hbound z
    (fieldFoldedWeight_integrable v hv z ζ F hFeven hwF)
    (fieldFoldedWeight_integrable v hv z ζ G hGeven hwG)
    (fieldFoldedWeight_mass_pos v hv z ζ F hFeven hwF)
    (fieldFoldedWeight_mass_pos v hv z ζ G hGeven hwG)

end InvariantIsing

end

end OAI
