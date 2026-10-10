import OAI.Probability.InvariantIsing.Fields.FieldSpinTransition

namespace OAI

/-! Even bounded tests of the tilted scalar position chain. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_even (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hFe : Function.Even F)
    (ha : Measurable a) (hae : Function.Even a) :
    Function.Even (fieldSpinTransition ζ v F a) := by
  intro z
  rw [fieldSpinTransition, fieldSpinTransition, integral_tilted_eq_div, integral_tilted_eq_div]
  have he : Function.Even (fun u => Real.exp (ζ * F u) * a u) := by
    intro u
    dsimp only
    rw [hFe u, hae u]
  have hm : Measurable (fun u => Real.exp (ζ * F u) * a u) :=
    (hF.const_mul ζ).exp.mul ha
  rw [field_gaussian_integral_reflect v z hm he,
    field_gaussian_integral_reflect v z (hF.const_mul ζ).exp
      (fun u => by rw [hFe u])]

lemma fieldSpinTransition_even_monotone (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hFe : Function.Even F) (hFg : HasLinearGrowth F)
    (ha : Measurable a) (hae : Function.Even a) (ham : MonotoneOn a (Ici 0))
    {K : ℝ} (haB : ∀ u, |a u| ≤ K) :
    MonotoneOn (fieldSpinTransition ζ v F a) (Ici 0) := by
  by_cases hv : v = 0
  · subst v
    intro x hx y hy hxy
    rw [fieldSpinTransition_zero_variance, fieldSpinTransition_zero_variance]
    exact ham hx hy hxy
  intro x hx y _hy hxy
  have h := field_gaussian_tilt_abs_parent_order v hv ζ F a hF hFe hFg
    ha ham haB hx hxy
  simpa only [fieldSpinTransition, field_even_abs hae] using h

lemma fieldSpinTransition_even_order (v : ℝ≥0) {ζ : ℝ} (hζ : 0 ≤ ζ)
    {F G a b : ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hFe : Function.Even F) (hGe : Function.Even G)
    (hFg : HasLinearGrowth F) (hGg : HasLinearGrowth G)
    (hFG : MonotoneOn (fun u => G u - F u) (Ici 0))
    (ha : Measurable a) (hb : Measurable b)
    (hae : Function.Even a) (hbe : Function.Even b)
    (ham : MonotoneOn a (Ici 0)) {K : ℝ}
    (haB : ∀ u, |a u| ≤ K) (hbB : ∀ u, |b u| ≤ K)
    (hab : ∀ u ∈ Ici (0 : ℝ), a u ≤ b u) (z : ℝ) :
    fieldSpinTransition ζ v F a z ≤ fieldSpinTransition ζ v G b z := by
  have hab' (u : ℝ) : a u ≤ b u := by
    rw [← field_even_abs hae u, ← field_even_abs hbe u]
    exact hab |u| (abs_nonneg u)
  by_cases hv : v = 0
  · subst v
    simpa only [fieldSpinTransition_zero_variance] using hab' z
  have h := field_gaussian_tilt_abs_payoff_order v hv hζ F G a hF hG hFe hGe
    hFg hGg hFG ha ham haB z
  have h' : fieldSpinTransition ζ v F a z ≤ fieldSpinTransition ζ v G a z := by
    simpa only [fieldSpinTransition, field_even_abs hae] using h
  exact h'.trans (fieldSpinTransition_mono_test ζ v G ha hb haB hbB hab' z)

end InvariantIsing

end

end OAI
