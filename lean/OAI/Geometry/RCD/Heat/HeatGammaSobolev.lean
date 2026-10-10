import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Sobolev regularity of heat energy densities from weak Bochner

Testing the actual weak Bochner inequality with heat regularizations of
the energy density bounds their Dirichlet energies uniformly. Lower
semicontinuity then puts the density itself in the Sobolev space.
-/

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem energyLp_le_of_heat_energy_bound (H : Lp ℝ 2 μ) (B : ℝ)
    (hb : ∀ s : ℝ, ∀ hs : 0 < s,
      energyForm μ hQ (heatSobolev μ hQ s hs H) (heatSobolev μ hQ s hs H) ≤ B) :
    energyLp μ H ≤ ENNReal.ofReal (B / 2) := by
  let s (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hs (k : ℕ) : 0 < s k := by dsimp only [s]; positivity
  have hconv : Tendsto (fun k => heatAt μ hQ (s k) H) atTop (𝓝 H) := by
    have ht := ((heatAt_continuous μ hQ H).tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [heatAt_zero, one_apply_eq_self, s, Function.comp_def] using ht
  apply (energyLp_le_liminf μ hconv).trans
  apply liminf_le_of_frequently_le'
  apply Eventually.frequently
  apply Eventually.of_forall
  intro k
  have hh := hb (s k) (hs k)
  rw [energyForm_self] at hh
  rw [← heatSobolev_toLp μ hQ (s k) (hs k) H]
  have he : energyLp μ (SobolevSpace.toLp μ hQ (heatSobolev μ hQ (s k) (hs k) H)) =
      ENNReal.ofReal (SobolevSpace.energy μ hQ (heatSobolev μ hQ (s k) (hs k) H)) :=
    (ENNReal.ofReal_toReal (heatSobolev μ hQ (s k) (hs k) H).property).symm
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  linarith

end RegularPointCoordinates

end

end OAI
