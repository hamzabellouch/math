import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFiniteContinuity

namespace OAI

/-! # Passing a uniform positive mean bound to the actual series limit -/

namespace Ostmann

open Filter MeasureTheory
open scoped Topology

 theorem density_integral_limit_bound (g : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (μ : Measure ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ n, Integrable (g n) μ) (hg0 : ∀ n t, 0 ≤ g n t)
    (hf : ∀ t, Tendsto (fun n => g n t) atTop (𝓝 (f t)))
    (hb : ∀ n, ∫ t, g n t ∂μ ≤ B) :
    Integrable f μ ∧ (∫ t, f t ∂μ) ≤ B := by
  have hf0 (t : ℝ) : 0 ≤ f t := ge_of_tendsto (hf t) (Filter.Eventually.of_forall (fun n => hg0 n t))
  have hfn : ∀ᵐ t ∂μ, Tendsto (fun n => g n t) atTop (𝓝 (f t)) := Filter.Eventually.of_forall hf
  have hn (n : ℕ) : (∫⁻ t, ‖g n t‖ₑ ∂μ) = ENNReal.ofReal (∫ t, g n t ∂μ) := by
    simp_rw [Real.enorm_eq_ofReal (hg0 n _)]
    exact (ofReal_integral_eq_lintegral_ofReal (hg n) (Filter.Eventually.of_forall (hg0 n))).symm
  have hlim : Filter.liminf (fun n => ∫⁻ t, ‖g n t‖ₑ ∂μ) atTop ≤ ENNReal.ofReal B := by
    apply liminf_le_of_frequently_le'
    exact Filter.Eventually.frequently (Filter.Eventually.of_forall (fun n => by
      rw [hn n]
      exact ENNReal.ofReal_le_ofReal (hb n)))
  have hint : Integrable f μ := integrable_of_tendsto hfn (fun n => (hg n).aestronglyMeasurable)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlim)
  refine ⟨hint, ?_⟩
  have hfat := (lintegral_enorm_le_liminf_of_tendsto hfn
    (fun n => (hg n).aestronglyMeasurable.aemeasurable.enorm)).trans hlim
  simp_rw [Real.enorm_eq_ofReal (hf0 _)] at hfat
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hf0)] at hfat
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hfat

end Ostmann

end OAI
