import OAI.Combinatorics.BalancedRyser.Selection.SelectionSuccessBound
import OAI.Combinatorics.BalancedRyser.Selection.SelectionUniformAssembly

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace Balanced.Selection.Process

universe u v w

def UniformConcentrationEstimate (p : Parameters) (ε : ℕ → ℝ) (q : ℕ) : Prop :=
  ∀ (I : Type u) (V : Type v) [Fintype I] [Fintype V],
    ∀ G : Input I V, GraphBounds G q p.c p.C →
      (snapshotPathLaw p q G).real
        {ω | ¬ FirstAbort.ConcentratedPath p q G
          (p.lastMainTime q (Fintype.card I)) ω} ≤ ε q

theorem uniformSuccessEstimate_of_concentration
    (p : Parameters) (hp : p.Admissible) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hconcentration : ∀ᶠ q : ℕ in atTop,
      UniformConcentrationEstimate.{u,v} p ε q) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ᶠ q : ℕ in atTop, UniformSuccessEstimate.{u,v} p δ q := by
  refine ⟨fun q => ε q + 18 * (q : ℝ) ^ 3 * postcheckTail p q, ?_, ?_⟩
  · simpa only [zero_add] using hε.add
      (tendsto_source_postcheck_bound p (Parameters.Pstar_pos hp).le)
  · obtain ⟨N, hN⟩ := exists_uniform_success_threshold.{u,v} p hp
    filter_upwards [hconcentration, eventually_ge_atTop N] with q hc hq
    intro I V _ _ G hG
    have hs := hN q hq G hG
    have hb := hc I V G hG
    change 1 - (ε q + 18 * (q : ℝ) ^ 3 * postcheckTail p q) ≤ _
    linarith

theorem selectionStatement_of_uniform_concentration_occupancy
    (hconcentration : ∀ p : Parameters, p.Admissible →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ q : ℕ in atTop, UniformConcentrationEstimate.{u,v} p ε q)
    (hoccupancy : ∀ p : Parameters, p.Admissible →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ q : ℕ in atTop, UniformOccupancyEstimate.{u,v,w} p ε q) :
    SelectionStatement.{u,v,w} := by
  apply selectionStatement_of_uniform_output_bounds ?_ hoccupancy
  intro p hp
  obtain ⟨ε, hε, hc⟩ := hconcentration p hp
  exact uniformSuccessEstimate_of_concentration p hp ε hε hc

end Balanced.Selection.Process

end

end OAI
