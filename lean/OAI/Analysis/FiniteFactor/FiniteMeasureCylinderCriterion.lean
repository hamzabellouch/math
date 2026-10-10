import Mathlib.MeasureTheory.Measure.Portmanteau

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- Finite-measure version of the neighborhood pi-system criterion. Total
mass convergence is required; zero limiting mass is handled separately. -/
theorem finiteMeasure_tendsto_of_piSystem {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [SecondCountableTopology Ω] [OpensMeasurableSpace Ω]
    [Nonempty Ω] {S : Set (Set Ω)} (hS : IsPiSystem S)
    {μ : ℕ → FiniteMeasure Ω} {ν : FiniteMeasure Ω}
    (hmeas : ∀ s ∈ S, MeasurableSet s)
    (hbasis : ∀ u : Set Ω, IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u)
    (hmass : Tendsto (fun n => (μ n).mass) atTop (𝓝 ν.mass))
    (hsets : ∀ s ∈ S, Tendsto (fun n => μ n s) atTop (𝓝 (ν s))) :
    Tendsto μ atTop (𝓝 ν) := by
  by_cases hν : ν = 0
  · subst ν
    exact FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hmass
  apply FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass _ hmass
  apply hS.tendsto_probabilityMeasure_of_tendsto_of_mem hmeas hbasis
  intro s hs
  have hv := ν.mass_nonzero_iff.mpr hν
  have he : ∀ᶠ n in atTop, μ n ≠ 0 := by
    filter_upwards [hmass.eventually (eventually_ne_nhds hv)] with n hn
    exact (μ n).mass_nonzero_iff.mp hn
  have hi : Tendsto (fun n => (μ n).mass⁻¹ * μ n s) atTop (𝓝 (ν.mass⁻¹ * ν s)) :=
    (hmass.inv₀ hv).mul (hsets s hs)
  rw [← ν.normalize_eq_of_nonzero hν s] at hi
  apply hi.congr'
  filter_upwards [he] with n hn
  exact ((μ n).normalize_eq_of_nonzero hn s).symm

end
end FiniteFactor

end OAI
