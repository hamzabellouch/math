import OAI.Analysis.CircleDomains.Topology.FiniteLevelComponents
import OAI.Analysis.CircleDomains.Topology.LevelComponentNontrivial

namespace OAI

/-! The actual level continua cover every interior trace point by the
countable nontrivial components of the full compact level section. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem full_level_null_image_of_approximation
    (φ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ} (hv : Continuous v)
    (hlim : TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop)
    {Q F : Set ℂ} (hQ : IsCompact Q) (hF : MeasurableSet F) (hFQ : F ⊆ interior Q)
    (u : ℕ → ℂ → ℝ) (hu : ∀ n, ContDiff ℝ 1 (u n)) {U : ℂ → ℝ}
    (hU : ∀ z ∈ Q, Tendsto (fun n => u n z) atTop (𝓝 (U z)))
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (e : ℕ → ℂ → ℝ≥0∞)
    (hgrad : ∀ n z, ENNReal.ofReal ‖fderiv ℝ (u n) z‖ ≤ g z+e n z)
    (hfinite : ∀ᵐ t ∂volume, (μH[1] : Measure ℂ) (Q ∩ {z | v z = t}) < ∞)
    (hgfinite : ∀ᵐ t ∂volume,
      (∫⁻ z in Q ∩ {z | v z = t}, g z ∂(μH[1] : Measure ℂ)) < ∞)
    (hgzero : ∀ᵐ t ∂volume,
      (∫⁻ z in F ∩ {z | v z = t}, g z ∂(μH[1] : Measure ℂ)) = 0)
    (herror : ∀ᵐ t ∂volume, Tendsto (fun n =>
      ∫⁻ z in Q ∩ {z | v z = t}, e n z ∂(μH[1] : Measure ℂ)) atTop (𝓝 0)) :
    ∀ᵐ t ∂volume, volume (U '' (F ∩ {z | v z = t})) = 0 := by
  have hFQ' : F ⊆ Q := hFQ.trans interior_subset
  filter_upwards [hfinite, hgfinite, hgzero, herror] with t ht hgt hgzt het
  have heq : F ∩ (Q ∩ {z | v z = t}) = F ∩ {z | v z = t} := by
    rw [← inter_assoc, inter_eq_left.mpr hFQ']
  have hK : IsCompact (Q ∩ {z | v z = t}) := hQ.inter_right (isClosed_eq hv continuous_const)
  have hh := finite_level_components_null_image hK ht u hu
    (fun z hz => hU z hz.1) g hg hgt hF (by rwa [heq]) e
    (fun n => Eventually.of_forall (hgrad n)) het (by
      intro z hzF hzK
      have hzt : v z = t := hzK.2
      subst t
      exact height_level_component_nontrivial φ hv hlim (hFQ hzF))
  rwa [heq] at hh

end CircleDomainRigidity

end

end OAI
