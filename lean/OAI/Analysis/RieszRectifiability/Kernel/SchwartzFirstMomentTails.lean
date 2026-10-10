import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSchwartzKernel

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set

theorem first_absolute_moment_bound_on_set {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (hm : Integrable (fun y => ‖y‖ * ‖g y‖) μ)
    (s : Set (Ambient d)) (hs : MeasurableSet s) (R : ℝ) (hR : 0 < R)
    (hsep : ∀ y ∈ s, R ≤ ‖y‖) :
    (∫ y in s, ‖g y‖ ∂μ) ≤ (∫ y, ‖y‖ * ‖g y‖ ∂μ) / R := by
  calc
    _ ≤ ∫ y in s, (‖y‖ * ‖g y‖) / R ∂μ := by
      apply integral_mono_ae hg.norm.restrict (hm.div_const R).restrict
      filter_upwards [ae_restrict_mem hs] with y hy
      apply (le_div_iff₀ hR).2
      nlinarith [mul_le_mul_of_nonneg_right (hsep y hy) (norm_nonneg (g y))]
    _ = (∫ y in s, ‖y‖ * ‖g y‖ ∂μ) / R := integral_div R _
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hR.le
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg y) (norm_nonneg (g y))) hm

theorem schwartz_first_absolute_moment_integrable {d : ℕ} (g : 𝓢(Ambient d, ℂ)) :
    Integrable (fun y : Ambient d => ‖y‖ * ‖g y‖) := by
  simpa only [pow_one] using! g.integrable_pow_mul (volume : Measure (Ambient d)) 1

theorem schwartz_first_absolute_moment_bound_on_set {d : ℕ}
    (g : 𝓢(Ambient d, ℂ)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (R : ℝ) (hR : 0 < R) (hsep : ∀ y ∈ s, R ≤ ‖y‖) :
    (∫ y in s, ‖g y‖) ≤ (∫ y : Ambient d, ‖y‖ * ‖g y‖) / R :=
  first_absolute_moment_bound_on_set volume g g.integrable
    (schwartz_first_absolute_moment_integrable g) s hs R hR hsep

end

end RieszRectifiability

end OAI
