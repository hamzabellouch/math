import Mathlib

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

theorem ae_zero_of_nonnegative_integral_limit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : ℕ → X → ℝ) (f : X → ℝ)
    (hi : ∀ j, Integrable (F j) μ) (hn : ∀ j x, 0 ≤ F j x)
    (hfm : Measurable f)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (f x)))
    (hint : Tendsto (fun j => ∫ x, F j x ∂μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, f x = 0 := by
  have hnn : ∀ᵐ x ∂μ, 0 ≤ f x := by
    filter_upwards [hlim] with x hx
    exact ge_of_tendsto hx (Eventually.of_forall (fun j => hn j x))
  have hL : Tendsto (fun j => ∫⁻ x, ENNReal.ofReal (F j x) ∂μ) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hint
    simpa only [Function.comp_def, ENNReal.ofReal_zero,
      ofReal_integral_eq_lintegral_ofReal (hi _) (Eventually.of_forall (hn _))] using! h
  have hFat : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ 0 := by
    calc
      _ = ∫⁻ x, liminf (fun j => ENNReal.ofReal (F j x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx).liminf_eq.symm
      _ ≤ liminf (fun j => ∫⁻ x, ENNReal.ofReal (F j x) ∂μ) atTop :=
        lintegral_liminf_le' (fun j => (hi j).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ = 0 := hL.liminf_eq
  have hz : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) = 0 :=
    (lintegral_eq_zero_iff hfm.ennreal_ofReal).mp (le_antisymm hFat (zero_le))
  filter_upwards [hz, hnn] with x hx hxnonneg
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx) hxnonneg

end

end RieszRectifiability

end OAI
