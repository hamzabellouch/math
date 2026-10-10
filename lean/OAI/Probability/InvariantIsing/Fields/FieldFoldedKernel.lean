import OAI.Probability.InvariantIsing.Fields.FieldLikelihoodRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace OAI

/-! Ordered folded Gaussian densities. These are the one-step comparisons
used in both the mixed and radial Ising-field derivatives. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

lemma field_tanh_monotone : Monotone Real.tanh := by
  intro x y hxy
  have hs : 0 ≤ Real.sinh (y - x) := Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr hxy)
  rw [Real.sinh_sub] at hs
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  exact (div_le_div_iff₀ (Real.cosh_pos x) (Real.cosh_pos y)).mpr (by nlinarith)

lemma field_tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  simpa only [Real.tanh_zero] using field_tanh_monotone hx

lemma field_scaled_tanh_mono {a b u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hu : 0 ≤ u) :
    a * Real.tanh (a * u) ≤ b * Real.tanh (b * u) := by
  exact mul_le_mul hab (field_tanh_monotone (mul_le_mul_of_nonneg_right hab hu))
    (field_tanh_nonneg (mul_nonneg ha hu)) (ha.trans hab)

lemma hasDerivAt_field_logcosh_mul (a x : ℝ) :
    HasDerivAt (fun z => Real.log (Real.cosh (a * z))) (a * Real.tanh (a * x)) x := by
  have h := (((Real.hasDerivAt_cosh (a * x)).comp x
    ((hasDerivAt_id x).const_mul a)).log (Real.cosh_pos (a * x)).ne')
  convert! h using 1
  simp only [Function.comp_apply, mul_one, Real.tanh_eq_sinh_div_cosh]
  ring

/-- Increasing the scale makes the log-cosh payoff difference even and
nondecreasing on the positive half-line. -/
lemma field_logcosh_scaled_difference_monotone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MonotoneOn (fun u => Real.log (Real.cosh (b * u)) - Real.log (Real.cosh (a * u))) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).log
      (fun _ => (Real.cosh_pos _).ne')).continuousOn.sub
        (((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).log
          (fun _ => (Real.cosh_pos _).ne')).continuousOn)
  · intro x _
    exact ((hasDerivAt_field_logcosh_mul b x).sub
      (hasDerivAt_field_logcosh_mul a x)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hd : HasDerivAt (fun u => Real.log (Real.cosh (b * u)) -
        Real.log (Real.cosh (a * u))) (b * Real.tanh (b * x) - a * Real.tanh (a * x)) x :=
      (hasDerivAt_field_logcosh_mul b x).sub (hasDerivAt_field_logcosh_mul a x)
    rw [hd.deriv]
    exact sub_nonneg.mpr (field_scaled_tanh_mono ha hab (le_of_lt hx))

lemma field_logcosh_scaled_difference_even (a b x : ℝ) :
    Real.log (Real.cosh (b * (-x))) - Real.log (Real.cosh (a * (-x))) =
      Real.log (Real.cosh (b * x)) - Real.log (Real.cosh (a * x)) := by
  simp only [mul_neg, Real.cosh_neg]

lemma field_cosh_ratio_monotone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MonotoneOn (fun u => Real.cosh (b * u) / Real.cosh (a * u)) (Ici 0) := by
  intro x hx y hy hxy
  have he := Real.exp_le_exp.mpr
    (field_logcosh_scaled_difference_monotone ha hab hx hy hxy)
  simpa only [Real.exp_sub, Real.exp_log (Real.cosh_pos _)] using he

def fieldFoldedWeight (v ζ : ℝ) (F : ℝ → ℝ) (z u : ℝ) : ℝ :=
  Real.exp (-u ^ 2 / (2 * v)) * Real.cosh ((z / v) * u) * Real.exp (ζ * F u)

lemma fieldFoldedWeight_pos (v ζ : ℝ) (F : ℝ → ℝ) (z u : ℝ) :
    0 < fieldFoldedWeight v ζ F z u :=
  mul_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _)) (Real.exp_pos _)

/-- The exact likelihood-ratio order in the absolute parent position. -/
lemma fieldFoldedWeight_parent_order {v : ℝ} (hv : 0 < v) (ζ : ℝ) (F : ℝ → ℝ)
    {z₀ z₁ : ℝ} (hz₀ : 0 ≤ z₀) (hzz : z₀ ≤ z₁)
    {u₀ u₁ : ℝ} (hu₀ : 0 ≤ u₀) (huu : u₀ ≤ u₁) :
    fieldFoldedWeight v ζ F z₁ u₀ * fieldFoldedWeight v ζ F z₀ u₁ ≤
      fieldFoldedWeight v ζ F z₁ u₁ * fieldFoldedWeight v ζ F z₀ u₀ := by
  have hr := field_cosh_ratio_monotone (div_nonneg hz₀ hv.le)
    ((div_le_div_iff_of_pos_right hv).mpr hzz) hu₀ (hu₀.trans huu) huu
  have hc := (div_le_div_iff₀ (Real.cosh_pos _) (Real.cosh_pos _)).mp hr
  let C := Real.exp (-u₀ ^ 2 / (2 * v)) * Real.exp (ζ * F u₀) *
    (Real.exp (-u₁ ^ 2 / (2 * v)) * Real.exp (ζ * F u₁))
  have hC : 0 ≤ C := (mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))
    (mul_pos (Real.exp_pos _) (Real.exp_pos _))).le
  convert! mul_le_mul_of_nonneg_left hc hC using 1 <;>
    dsimp only [fieldFoldedWeight, C] <;> ring

/-- Increasing the even payoff by an increasing function raises the
folded transition in likelihood-ratio order. -/
lemma fieldFoldedWeight_payoff_order (v : ℝ) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (F G : ℝ → ℝ) (hFG : MonotoneOn (fun u => G u - F u) (Ici 0))
    (z : ℝ) {u₀ u₁ : ℝ} (hu₀ : 0 ≤ u₀) (huu : u₀ ≤ u₁) :
    fieldFoldedWeight v ζ G z u₀ * fieldFoldedWeight v ζ F z u₁ ≤
      fieldFoldedWeight v ζ G z u₁ * fieldFoldedWeight v ζ F z u₀ := by
  have hdiff := mul_le_mul_of_nonneg_left (hFG hu₀ (hu₀.trans huu) huu) hζ
  have he : Real.exp (ζ * G u₀ + ζ * F u₁) ≤ Real.exp (ζ * G u₁ + ζ * F u₀) :=
    Real.exp_le_exp.mpr (by nlinarith)
  let C := Real.exp (-u₀ ^ 2 / (2 * v)) * Real.cosh ((z / v) * u₀) *
    (Real.exp (-u₁ ^ 2 / (2 * v)) * Real.cosh ((z / v) * u₁))
  have hC : 0 ≤ C := (mul_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _))
    (mul_pos (Real.exp_pos _) (Real.cosh_pos _))).le
  rw [Real.exp_add, Real.exp_add] at he
  convert! mul_le_mul_of_nonneg_left he hC using 1 <;>
    dsimp only [fieldFoldedWeight, C] <;> ring

/-- The parent comparison acts on every bounded increasing test under the
actual folded density, after its Gaussian integrability is supplied. -/
theorem fieldFolded_parent_expectation_le {v : ℝ} (hv : 0 < v)
    (ζ : ℝ) (F f : ℝ → ℝ) (hf : Measurable f)
    (hmono : MonotoneOn f (Ici 0)) {C : ℝ} (hbound : ∀ u, |f u| ≤ C)
    {z₀ z₁ : ℝ} (hz₀ : 0 ≤ z₀) (hzz : z₀ ≤ z₁)
    (h₀ : Integrable (fieldFoldedWeight v ζ F z₀) (volume.restrict (Ici 0)))
    (h₁ : Integrable (fieldFoldedWeight v ζ F z₁) (volume.restrict (Ici 0)))
    (hm₀ : 0 < ∫ u in Ici 0, fieldFoldedWeight v ζ F z₀ u)
    (hm₁ : 0 < ∫ u in Ici 0, fieldFoldedWeight v ζ F z₁ u) :
    (∫ u in Ici 0, f u * fieldFoldedWeight v ζ F z₀ u) /
        (∫ u in Ici 0, fieldFoldedWeight v ζ F z₀ u) ≤
      (∫ u in Ici 0, f u * fieldFoldedWeight v ζ F z₁ u) /
        (∫ u in Ici 0, fieldFoldedWeight v ζ F z₁ u) := by
  have hb : ∀ᵐ u ∂volume.restrict (Ici (0 : ℝ)), ‖f u‖ ≤ C :=
    Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hbound u)
  exact field_likelihood_ratio_expectation_le (volume.restrict (Ici 0)) _ _ f
    (ae_restrict_mem measurableSet_Ici) hmono
    (fun x hx y _hxy hxy => fieldFoldedWeight_parent_order hv ζ F hz₀ hzz hx hxy)
    h₀ h₁ (h₀.bdd_mul hf.aestronglyMeasurable hb)
    (h₁.bdd_mul hf.aestronglyMeasurable hb) hm₀ hm₁

/-- The payoff comparison acts on the same bounded increasing tests. -/
theorem fieldFolded_payoff_expectation_le (v : ℝ) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (F G f : ℝ → ℝ) (hFG : MonotoneOn (fun u => G u - F u) (Ici 0))
    (hf : Measurable f) (hmono : MonotoneOn f (Ici 0))
    {C : ℝ} (hbound : ∀ u, |f u| ≤ C) (z : ℝ)
    (h₀ : Integrable (fieldFoldedWeight v ζ F z) (volume.restrict (Ici 0)))
    (h₁ : Integrable (fieldFoldedWeight v ζ G z) (volume.restrict (Ici 0)))
    (hm₀ : 0 < ∫ u in Ici 0, fieldFoldedWeight v ζ F z u)
    (hm₁ : 0 < ∫ u in Ici 0, fieldFoldedWeight v ζ G z u) :
    (∫ u in Ici 0, f u * fieldFoldedWeight v ζ F z u) /
        (∫ u in Ici 0, fieldFoldedWeight v ζ F z u) ≤
      (∫ u in Ici 0, f u * fieldFoldedWeight v ζ G z u) /
        (∫ u in Ici 0, fieldFoldedWeight v ζ G z u) := by
  have hb : ∀ᵐ u ∂volume.restrict (Ici (0 : ℝ)), ‖f u‖ ≤ C :=
    Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hbound u)
  exact field_likelihood_ratio_expectation_le (volume.restrict (Ici 0)) _ _ f
    (ae_restrict_mem measurableSet_Ici) hmono
    (fun x hx y _hy hxy => fieldFoldedWeight_payoff_order v hζ F G hFG z hx hxy)
    h₀ h₁ (h₀.bdd_mul hf.aestronglyMeasurable hb)
    (h₁.bdd_mul hf.aestronglyMeasurable hb) hm₀ hm₁

end InvariantIsing

end

end OAI
