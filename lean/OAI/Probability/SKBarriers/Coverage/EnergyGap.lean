import Mathlib
import OAI.Probability.SKBarriers.Coverage.FiniteTemperatureBound
import OAI.Probability.SKBarriers.Coverage.EquilibriumEnergy

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem equilibrium_energy_gap {β : ℝ} (hβ : 1 < β) :
    ∃ e₀ : ℝ, e₀ < β/2 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      equilibriumEnergy β N ≤ e₀ := by
  obtain ⟨γ,hβγ,hsec⟩ := exists_strict_finiteParisiInf_secant hβ
  obtain ⟨e₀,hleft,hright⟩ := exists_between hsec
  have hd : 0 < γ-β := sub_pos.mpr hβγ
  have HT : Tendsto (fun N : ℕ => (finiteParisiInf γ-quenchedPressure β N)/(γ-β))
      atTop (𝓝 ((finiteParisiInf γ-finiteParisiInf β)/(γ-β))) :=
    (tendsto_const_nhds.sub (quenchedPressure_tendsto_finiteParisiInf
      (lt_trans zero_lt_one hβ))).div_const (γ-β)
  have HE := HT.eventually (eventually_lt_nhds hleft)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp HE
  refine ⟨e₀,hright,max N₀ 1,?_⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N₀ 1).trans hN)
  have HU := equilibriumEnergy_le_secant hNpos hβγ
  have HQ := quenched_le_finiteParisiInf hNpos γ
  have HD := div_le_div_of_nonneg_right (sub_le_sub_right HQ (quenchedPressure β N)) hd.le
  exact (HU.trans HD).trans (hN₀ N ((le_max_left N₀ 1).trans hN)).le

theorem pressure_derivative_energy_gap {β : ℝ} (hβ : 1 < β) :
    ∃ e₀ : ℝ, e₀ < β/2 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      HasDerivAt (fun γ => quenchedPressure γ N) (equilibriumEnergy β N) β ∧
      equilibriumEnergy β N ≤ e₀ := by
  obtain ⟨e₀,he₀,N₀,hN₀⟩ := equilibrium_energy_gap hβ
  refine ⟨e₀,he₀,max N₀ 1,?_⟩
  intro N hN
  exact ⟨quenchedPressure_hasDerivAt (lt_of_lt_of_le Nat.zero_lt_one
    ((le_max_right N₀ 1).trans hN)) β,hN₀ N ((le_max_left N₀ 1).trans hN)⟩
end SK.Analytic

end
end

end

end OAI
