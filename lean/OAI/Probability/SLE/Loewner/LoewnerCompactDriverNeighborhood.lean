import OAI.Probability.SLE.Loewner.LoewnerCompactSurvival
import OAI.Probability.SLE.Loewner.LoewnerInverseDriverContinuity

namespace OAI

/-! Compact survival holds throughout a uniform neighborhood of a fixed
driver, with no regularity assumption on the perturbed trace beyond its
actual capacity witness. -/
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SLEExactGauge

theorem driver_neighborhood_preserves_compact
    {V : ℝ≥0 → ℝ} {β : ℝ≥0 → ℂ} {H J : ℝ≥0 → ℂ → ℂ}
    (hv : IsCapacityTwoWitness V β H J) (T : ℝ≥0)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ survivingDomain β T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
      (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F →
      (∀ t ∈ Icc 0 T, |U t-V t| ≤ δ) → K ⊆ survivingDomain γ T := by
  classical
  by_contra hn
  push Not at hn
  have hc (n : ℕ) := hn ((n+1:ℝ)⁻¹) (by positivity)
  choose U γ G F hw hclose hfail using hc
  have hδ : Tendsto (fun n : ℕ => (n+1:ℝ)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hl := inverse_maps_locally_uniform_of_drivers U γ G F hw hv T
    (fun n : ℕ => (n+1:ℝ)⁻¹) hδ hclose
  have he := compact_survival_of_inverse_convergence U γ G F hw hv T hl hK hKD
  obtain ⟨n,hn⟩ := he.exists
  exact hfail n hn

end SLEExactGauge

end

end OAI
