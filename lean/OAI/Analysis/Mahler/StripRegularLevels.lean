import OAI.Analysis.Mahler.StripLevelGeometry
import Mathlib.Topology.Order.MonotoneConvergence

namespace OAI

noncomputable section
namespace SymmetricMahler
open Set Filter MeasureTheory
open scoped Topology ENNReal
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Continuity from below, stated as convergence in the extended nonnegative reals. -/
theorem tendsto_strip_sublevel_mass (A : J → I → ℝ) (m : ℕ)
    (μ : Measure ((I → ℝ) × (I → ℝ))) (ρ : ((I → ℝ) × (I → ℝ)) → ℝ≥0∞) :
    Tendsto (fun k => ∫⁻ z in {z | z ∈ stripDomain A ∧ stripTau A m z < stripRegularLevel k}, ρ z ∂μ)
      atTop (𝓝 (∫⁻ z in {z | z ∈ stripDomain A ∧ stripTau A m z < 1}, ρ z ∂μ)) := by
  rw [strip_mass_exhaustion_iSup A m μ ρ]
  apply tendsto_atTop_iSup
  intro a b hab
  exact lintegral_mono_set (strip_regular_sublevels_monotone A m hab)

/-- The rank and exponent hypotheses yield an increasing
regular exhaustion with compact boundaries, without a regular-value premise. -/
theorem manuscript_strip_regular_exhaustion (A : J → I → ℝ)
    (hRank : Module.finrank ℝ (LinearMap.range (measurementLinear A)) = Fintype.card I)
    {m : ℕ} (hm : 2 ≤ m) :
    StrictMono stripRegularLevel ∧
    (∀ k, stripRegularLevel k ∈ Ioo (0 : ℝ) 1) ∧
    Tendsto stripRegularLevel atTop (𝓝 1) ∧
    (∀ k z, z ∈ stripDomain A → stripTau A m z = stripRegularLevel k →
      Function.Surjective (fderiv ℝ (stripTau A m) z)) ∧
    (∀ k, IsCompact {z | z ∈ stripDomain A ∧ stripTau A m z = stripRegularLevel k}) ∧
    (∀ k, frontier {z | z ∈ stripDomain A ∧ stripTau A m z < stripRegularLevel k} =
      {z | z ∈ stripDomain A ∧ stripTau A m z = stripRegularLevel k}) ∧
    (⋃ k, {z | z ∈ stripDomain A ∧ stripTau A m z < stripRegularLevel k}) =
      {z | z ∈ stripDomain A ∧ stripTau A m z < 1} := by
  have hA := (measurement_full_rank_iff A).mp hRank
  have hm0 : 0 < m := by omega
  obtain ⟨hs, hi, ht, hr⟩ := strip_regular_value_sequence A hA hm0
  exact ⟨hs, hi, ht, hr,
    fun k => isCompact_strip_level A hA hm0 (hi k).1.le (hi k).2,
    fun k => frontier_strip_sublevel A hA hm0 (hi k).1 (hi k).2,
    strip_regular_sublevels_union A m⟩

end SymmetricMahler

end

end OAI
