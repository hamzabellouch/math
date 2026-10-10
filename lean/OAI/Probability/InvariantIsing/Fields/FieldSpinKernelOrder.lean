import OAI.Probability.InvariantIsing.Fields.FieldSpinFolding

namespace OAI

/-! Monotonicity of the physical conditional-spin transition. This keeps
the spin observable, rather than the derivative in rescaled coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_spin_test_measurable {a : ℝ → ℝ} (ha : Measurable a) (v z : ℝ) :
    Measurable (fun u => a u * Real.tanh ((z / v) * u)) := by
  simp only [Real.tanh_eq]
  fun_prop

lemma field_spin_test_bound {a : ℝ → ℝ} {B : ℝ} (ha : ∀ u, |a u| ≤ B) (v z u : ℝ) :
    |a u * Real.tanh ((z / v) * u)| ≤ B := by
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (field_abs_tanh_le_one _) (abs_nonneg _)).trans
    (by simpa only [mul_one] using ha u)

lemma field_spin_test_monotone {a : ℝ → ℝ} (ha : MonotoneOn a (Ici 0))
    (hapos : ∀ u ∈ Ici (0 : ℝ), 0 ≤ a u) {v z : ℝ} (hv : 0 < v) (hz : 0 ≤ z) :
    MonotoneOn (fun u => a u * Real.tanh ((z / v) * u)) (Ici 0) := by
  intro x hx y hy hxy
  exact mul_le_mul (ha hx hy hxy)
    (field_tanh_monotone (mul_le_mul_of_nonneg_left hxy (div_nonneg hz hv.le)))
    (field_tanh_nonneg (mul_nonneg (div_nonneg hz hv.le) hx)) (hapos y hy)

private lemma field_spin_exp_integrable (v : ℝ≥0) (z ζ : ℝ)
    (F a : ℝ → ℝ) (hF : Measurable F) (hgrowth : HasLinearGrowth F)
    (ha : Measurable a) {B : ℝ} (hbound : ∀ u, |a u| ≤ B) :
    Integrable (fun u => Real.exp (ζ * F u) * a u) (gaussianReal z v) := by
  have hi := (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v)
    hF hgrowth ζ).bdd_mul ha.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hbound u))
  simpa only [mul_comm] using hi

lemma field_gaussian_tilt_odd_eq_abs (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F a : ℝ → ℝ) (hF : Measurable F) (hFeven : Function.Even F)
    (hgrowth : HasLinearGrowth F) (ha : Measurable a) (haodd : Function.Odd a)
    {B : ℝ} (hbound : ∀ u, |a u| ≤ B) :
    (∫ u, a u ∂(gaussianReal z v).tilted (fun u => ζ * F u)) =
      ∫ u, a |u| * Real.tanh ((z / v) * |u|)
        ∂(gaussianReal z v).tilted (fun u => ζ * F u) := by
  let f := fun u => a u * Real.tanh ((z / (v : ℝ)) * u)
  have hf : Measurable f := field_spin_test_measurable ha v z
  have hb : ∀ u, |f u| ≤ B := field_spin_test_bound hbound v z
  have hw := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v)
    hF hgrowth ζ
  rw [field_gaussian_tilt_odd_integral_eq_folded v hv z ζ F a hFeven haodd
    (field_spin_exp_integrable v z ζ F a hF hgrowth ha hbound) hw]
  rw [integral_tilted_eq_div]
  exact (field_gaussian_folded_ratio v hv z ζ F f hFeven
    (field_spin_exp_integrable v z ζ F (fun u => f |u|) hF hgrowth
      (hf.comp measurable_abs) (fun u => hb |u|)) hw).symm

/-- Parent, payoff and physical spin-observable comparisons in one actual
Gaussian transition. This is the backward induction step in fld:radial. -/
theorem field_gaussian_spin_transition_order (v : ℝ≥0) (hv : v ≠ 0) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (F G a b : ℝ → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFeven : Function.Even F) (hGeven : Function.Even G)
    (hFgrowth : HasLinearGrowth F) (hGgrowth : HasLinearGrowth G)
    (hFG : MonotoneOn (fun u => G u - F u) (Ici 0))
    (ha : Measurable a) (hb : Measurable b) (haodd : Function.Odd a) (hbodd : Function.Odd b)
    (hamono : MonotoneOn a (Ici 0)) (hapos : ∀ u ∈ Ici (0 : ℝ), 0 ≤ a u)
    (hab : ∀ u ∈ Ici (0 : ℝ), a u ≤ b u)
    {B : ℝ} (haB : ∀ u, |a u| ≤ B) (hbB : ∀ u, |b u| ≤ B)
    {z₀ z₁ : ℝ} (hz₀ : 0 ≤ z₀) (hzz : z₀ ≤ z₁) :
    (∫ u, a u ∂(gaussianReal z₀ v).tilted (fun u => ζ * F u)) ≤
      ∫ u, b u ∂(gaussianReal z₁ v).tilted (fun u => ζ * G u) := by
  let f := fun u => a u * Real.tanh ((z₀ / (v : ℝ)) * u)
  let g := fun u => b u * Real.tanh ((z₁ / (v : ℝ)) * u)
  have hf : Measurable f := field_spin_test_measurable ha v z₀
  have hg : Measurable g := field_spin_test_measurable hb v z₁
  have hfB : ∀ u, |f u| ≤ B := field_spin_test_bound haB v z₀
  have hgB : ∀ u, |g u| ≤ B := field_spin_test_bound hbB v z₁
  have hvp : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hfmono : MonotoneOn f (Ici 0) := field_spin_test_monotone hamono hapos hvp hz₀
  have hp := field_gaussian_tilt_abs_parent_order v hv ζ F f hF hFeven hFgrowth
    hf hfmono hfB hz₀ hzz
  have hq := field_gaussian_tilt_abs_payoff_order v hv hζ F G f hF hG hFeven hGeven
    hFgrowth hGgrowth hFG hf hfmono hfB z₁
  have htest : ∀ u, f |u| ≤ g |u| := by
    intro u
    have hu : |u| ∈ Ici (0 : ℝ) := abs_nonneg u
    exact mul_le_mul (hab |u| hu)
      (field_tanh_monotone (mul_le_mul_of_nonneg_right
        ((div_le_div_iff_of_pos_right hvp).mpr hzz) (abs_nonneg u)))
      (field_tanh_nonneg (mul_nonneg (div_nonneg hz₀ hvp.le) (abs_nonneg u)))
      ((hapos |u| hu).trans (hab |u| hu))
  have hfg : (∫ u, f |u| ∂(gaussianReal z₁ v).tilted (fun u => ζ * G u)) ≤
      ∫ u, g |u| ∂(gaussianReal z₁ v).tilted (fun u => ζ * G u) := by
    apply integral_mono
      (Integrable.of_bound (hf.comp measurable_abs).aestronglyMeasurable B
        (Filter.Eventually.of_forall (fun u => by simpa only [Function.comp_apply, Real.norm_eq_abs] using hfB |u|)))
      (Integrable.of_bound (hg.comp measurable_abs).aestronglyMeasurable B
        (Filter.Eventually.of_forall (fun u => by simpa only [Function.comp_apply, Real.norm_eq_abs] using hgB |u|))) htest
  have he₀ := field_gaussian_tilt_odd_eq_abs v hv z₀ ζ F a hF hFeven hFgrowth ha haodd haB
  have he₁ := field_gaussian_tilt_odd_eq_abs v hv z₁ ζ G b hG hGeven hGgrowth hb hbodd hbB
  exact he₀.trans_le ((hp.trans hq).trans (hfg.trans_eq he₁.symm))

end InvariantIsing

end

end OAI
