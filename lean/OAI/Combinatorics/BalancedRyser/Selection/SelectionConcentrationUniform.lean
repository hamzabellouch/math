import OAI.Combinatorics.BalancedRyser.Selection.SelectionFirstAbort
import OAI.Combinatorics.BalancedRyser.Selection.SelectionSourceConcentration

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace Balanced.Selection.Process
universe u v w
attribute [local instance] Classical.propDecidable

theorem exists_uniformConcentratedPath_estimate (p : Parameters) (hp : p.Admissible) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ q : ℕ in atTop,
        ∀ (I : Type u) (V : Type v) [Fintype I] [Fintype V],
        ∀ G : Input I V, GraphBounds G q p.c p.C →
          (snapshotPathLaw p q G).real {ω | ¬ FirstAbort.ConcentratedPath p q G
            (p.lastMainTime q (Fintype.card I)) ω} ≤ ε q := by
  refine ⟨trackConcentrationError p, tendsto_trackConcentrationError hp, ?_⟩
  obtain ⟨Q, hQ⟩ := exists_source_concentration_threshold hp
  filter_upwards [eventually_ge_atTop Q] with q hq
  obtain ⟨hq2, hPq, hDd, hDv⟩ := hQ q hq
  intro I V _ _ G hG
  have h := source_true_count_failure_probability_le hp hG hq2 hPq hDd hDv
  convert h using 1
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, FirstAbort.ConcentratedPath,
    FirstAbort.StateConcentration, domain, degree, initialState, currentVertices, slotVertices,
    Finset.mem_univ, Finset.filter_true, Finset.inter_univ]
  apply not_congr
  constructor
  · intro h t S ht hS
    exact h t ht S hS
  · intro h t ht S hS
    exact h t S ht hS
end Balanced.Selection.Process

end

end OAI
