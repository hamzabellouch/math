import OAI.Probability.InvariantIsing.Fields.FieldSpinKernelOrder
import Mathlib.Probability.Moments.Variance

namespace OAI

/-! The scalar physical-spin transition and its bounded martingale
properties, including degenerate covariance increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldSpinTransition (ζ : ℝ) (v : ℝ≥0) (F a : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ u, a u ∂(gaussianReal z v).tilted (fun u => ζ * F u)

lemma fieldSpinTransition_zero_variance (ζ : ℝ) (F a : ℝ → ℝ) (z : ℝ) :
    fieldSpinTransition ζ 0 F a z = a z := by
  rw [fieldSpinTransition, integral_tilted_eq_div, gaussianReal_zero_var]
  simp only [integral_dirac]
  exact mul_div_cancel_left₀ (a z) (Real.exp_ne_zero _)

lemma fieldSpinTransition_eq_standard (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (ha : Measurable a) (z : ℝ) :
    fieldSpinTransition ζ v F a z = gaussianTiltAverage v ζ F a z := by
  rw [fieldSpinTransition, integral_tilted_eq_div, gaussianTiltAverage_eq_div]
  have hnum : Measurable (fun u => Real.exp (ζ * F u) * a u) := (hF.const_mul ζ).exp.mul ha
  have hden : Measurable (fun u => Real.exp (ζ * F u)) := (hF.const_mul ζ).exp
  rw [field_gaussian_integral_shift v z hnum, field_gaussian_integral_shift v z hden]
  have hnums : Measurable (fun u => Real.exp (ζ * F (z + u)) * a (z + u)) :=
    hnum.comp (measurable_const.add measurable_id)
  have hdens : Measurable (fun u => Real.exp (ζ * F (z + u))) :=
    hden.comp (measurable_const.add measurable_id)
  rw [integral_gaussianReal_zero_eq_standard v
      (F := fun u => Real.exp (ζ * F (z + u)) * a (z + u)) hnums,
    integral_gaussianReal_zero_eq_standard v
      (F := fun u => Real.exp (ζ * F (z + u))) hdens]

lemma measurable_fieldSpinTransition (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (ha : Measurable a) :
    Measurable (fieldSpinTransition ζ v F a) := by
  have hnum : Measurable (fun p : ℝ × ℝ =>
      Real.exp (ζ * F (p.1 + Real.sqrt (v : ℝ) * p.2)) *
        a (p.1 + Real.sqrt (v : ℝ) * p.2)) := by fun_prop
  have hden : Measurable (fun p : ℝ × ℝ =>
      Real.exp (ζ * F (p.1 + Real.sqrt (v : ℝ) * p.2))) := by fun_prop
  have he : fieldSpinTransition ζ v F a = fun z =>
      (∫ u, Real.exp (ζ * F (z + Real.sqrt (v : ℝ) * u)) *
        a (z + Real.sqrt (v : ℝ) * u) ∂gaussianReal 0 1) /
      (∫ u, Real.exp (ζ * F (z + Real.sqrt (v : ℝ) * u)) ∂gaussianReal 0 1) := by
    funext z
    rw [fieldSpinTransition_eq_standard ζ v hF ha z, gaussianTiltAverage_eq_div]
  rw [he]
  exact hnum.stronglyMeasurable.integral_prod_right'.measurable.div
    hden.stronglyMeasurable.integral_prod_right'.measurable

lemma fieldSpinTransition_bound (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hgrowth : HasLinearGrowth F)
    {B : ℝ} (haB : ∀ u, |a u| ≤ B) (z : ℝ) :
    |fieldSpinTransition ζ v F a z| ≤ B := by
  have hw := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hgrowth ζ
  have : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    MeasureTheory.isProbabilityMeasure_tilted hw
  have hb := norm_integral_le_of_norm_le_const (f := a) (C := B)
    (μ := (gaussianReal z v).tilted (fun u => ζ * F u))
    (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using haB u))
  simpa only [fieldSpinTransition, Real.norm_eq_abs, measureReal_def, measure_univ,
    ENNReal.toReal_one, mul_one] using hb

lemma fieldSpinTransition_square_le (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hgrowth : HasLinearGrowth F) (ha : Measurable a)
    {B : ℝ} (haB : ∀ u, |a u| ≤ B) (z : ℝ) :
    (fieldSpinTransition ζ v F a z) ^ 2 ≤
      fieldSpinTransition ζ v F (fun u => (a u) ^ 2) z := by
  have hw := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hgrowth ζ
  have : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    MeasureTheory.isProbabilityMeasure_tilted hw
  have hm : MemLp a 2 ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    MemLp.of_bound ha.aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using haB u))
  have hv := variance_nonneg a ((gaussianReal z v).tilted (fun u => ζ * F u))
  rw [variance_eq_sub hm] at hv
  change 0 ≤ fieldSpinTransition ζ v F (fun u => (a u) ^ 2) z -
    (fieldSpinTransition ζ v F a z) ^ 2 at hv
  linarith

lemma fieldSpinTransition_odd (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hEven : Function.Even F)
    (ha : Measurable a) (hOdd : Function.Odd a) :
    Function.Odd (fieldSpinTransition ζ v F a) := by
  intro z
  rw [fieldSpinTransition, fieldSpinTransition, integral_tilted_eq_div, integral_tilted_eq_div]
  have hnum : Measurable (fun u => Real.exp (ζ * F u) * a u) := (hF.const_mul ζ).exp.mul ha
  have hn : (∫ u, Real.exp (ζ * F u) * a u ∂gaussianReal (-z) v) =
      -(∫ u, Real.exp (ζ * F u) * a u ∂gaussianReal z v) := by
    rw [← gaussianReal_map_neg (μ := z) (v := v),
      integral_map measurable_neg.aemeasurable hnum.aestronglyMeasurable]
    calc
      _ = ∫ u, -(Real.exp (ζ * F u) * a u) ∂gaussianReal z v := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u => by
          change Real.exp (ζ * F (-u)) * a (-u) = -(Real.exp (ζ * F u) * a u)
          rw [hEven u, hOdd u]
          ring)
      _ = _ := integral_neg _
  have hd := field_gaussian_integral_reflect v z (hF.const_mul ζ).exp
    (fun u => by rw [hEven u])
  rw [hn, hd, neg_div]

lemma fieldSpinTransition_nonneg (ζ : ℝ) (v : ℝ≥0)
    {F a : ℝ → ℝ} (hF : Measurable F) (hEven : Function.Even F)
    (hgrowth : HasLinearGrowth F) (ha : Measurable a) (hOdd : Function.Odd a)
    (hapos : ∀ u ∈ Ici (0 : ℝ), 0 ≤ a u)
    {B : ℝ} (haB : ∀ u, |a u| ≤ B) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ fieldSpinTransition ζ v F a z := by
  by_cases hv : v = 0
  · subst v
    rw [fieldSpinTransition_zero_variance]
    exact hapos z hz
  have he := field_gaussian_tilt_odd_eq_abs v hv z ζ F a hF hEven hgrowth ha hOdd haB
  rw [fieldSpinTransition, he]
  apply integral_nonneg
  intro u
  exact mul_nonneg (hapos |u| (abs_nonneg u))
    (field_tanh_nonneg (mul_nonneg (div_nonneg hz v.coe_nonneg) (abs_nonneg u)))

lemma fieldSpinTransition_monotone {ζ : ℝ} (hζ : 0 ≤ ζ) (v : ℝ≥0)
    {F a : ℝ → ℝ} (hF : Measurable F) (hEven : Function.Even F)
    (hgrowth : HasLinearGrowth F) (ha : Measurable a) (hOdd : Function.Odd a)
    (hamono : MonotoneOn a (Ici 0)) (hapos : ∀ u ∈ Ici (0 : ℝ), 0 ≤ a u)
    {B : ℝ} (haB : ∀ u, |a u| ≤ B) :
    MonotoneOn (fieldSpinTransition ζ v F a) (Ici 0) := by
  by_cases hv : v = 0
  · subst v
    intro x hx y hy hxy
    rw [fieldSpinTransition_zero_variance, fieldSpinTransition_zero_variance]
    exact hamono hx hy hxy
  intro x hx y _hy hxy
  exact field_gaussian_spin_transition_order v hv hζ F F a a hF hF hEven hEven hgrowth hgrowth
    (by intro u _ w _ _; simp only [sub_self, le_refl])
    ha ha hOdd hOdd hamono hapos (fun _ _ => le_rfl) haB haB hx hxy

lemma fieldSpinTransition_mono_test (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ)
    {a b : ℝ → ℝ} (ha : Measurable a) (hb : Measurable b) {A B : ℝ}
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B)
    (hab : ∀ u, a u ≤ b u) (z : ℝ) :
    fieldSpinTransition ζ v F a z ≤ fieldSpinTransition ζ v F b z := by
  exact integral_mono
    (Integrable.of_bound ha.aestronglyMeasurable A
      (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using haB u)))
    (Integrable.of_bound hb.aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hbB u))) hab

end InvariantIsing

end

end OAI
