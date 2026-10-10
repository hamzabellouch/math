import OAI.Analysis.KadisonKastler.GaussianStateAverage

namespace OAI

/-! # Real-translation covariance of the Gaussian analytic orbit -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem stateActionOrbit_add (a : H →L[ℂ] H) (s t : ℝ) :
    stateActionOrbit U a (s + t) =
      unitaryConj (U (Multiplicative.ofAdd s)) (stateActionOrbit U a t) := by
  change unitaryConj (U (Multiplicative.ofAdd s * Multiplicative.ofAdd t)) a = _
  rw [map_mul, unitaryConj_mul]
  rfl

theorem gaussianStateAverage_covariance
    (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z : ℂ) (s : ℝ) :
    unitaryConj (U (Multiplicative.ofAdd s)) (gaussianStateAverage U hU a r hr z) =
      gaussianStateAverage U hU a r hr (z + s) := by
  apply ContinuousLinearMap.ext
  intro x
  let u := U (Multiplicative.ofAdd s)
  have hI := integrable_weighted_operator_vector volume (gaussianStateKernel r z)
    (gaussianStateKernel_integrable hr z) (stateActionOrbit U a)
    (fun y => (stateActionOrbit_continuous U hU a y).aestronglyMeasurable)
    ‖a‖ (Filter.Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)
    (star (u : H →L[ℂ] H) x)
  change (u : H →L[ℂ] H) (∫ t : ℝ, gaussianStateKernel r z t •
      stateActionOrbit U a t (star (u : H →L[ℂ] H) x)) =
    ∫ t : ℝ, gaussianStateKernel r (z + s) t • stateActionOrbit U a t x
  rw [← (u : H →L[ℂ] H).integral_comp_comm hI]
  calc
    (∫ t : ℝ, (u : H →L[ℂ] H) (gaussianStateKernel r z t •
        stateActionOrbit U a t (star (u : H →L[ℂ] H) x))) =
      ∫ t : ℝ, gaussianStateKernel r z t • stateActionOrbit U a (s + t) x := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [map_smul, stateActionOrbit_add]
        rfl
    _ = ∫ t : ℝ, gaussianStateKernel r (z + s) (s + t) • stateActionOrbit U a (s + t) x := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [gaussianStateKernel_translate, add_sub_cancel_left]
    _ = _ := integral_add_left_eq_self
      (fun t : ℝ => gaussianStateKernel r (z + s) t • stateActionOrbit U a t x) s

end

end KadisonKastler

end OAI
