import OAI.Probability.SpanningForest.Definitions
import OAI.Probability.SpanningForest.CoordinateTruncation

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem336.CoordinateTruncation

def finiteEdges (K : FiniteSubgraphCode) : Finset EdgeCode :=
  K.2.subtype (fun p => p.1 < p.2)

@[simp] theorem mem_finiteEdges (K : FiniteSubgraphCode) (e : EdgeCode) :
    e ∈ finiteEdges K ↔ e.1 ∈ K.2 := by
  simp [finiteEdges]

def graphEdges (G : GraphCode) : Set EdgeCode :=
  {e | Adj G e.1.1 e.1.2}

theorem exhaustion_finiteEdges_monotone {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    Monotone (fun n => finiteEdges (H n)) := by
  apply monotone_nat_of_le_succ
  intro n e he
  apply (mem_finiteEdges (H (n + 1)) e).mpr
  exact (hH.2.1 n).2 ((mem_finiteEdges (H n) e).mp he)

theorem exhaustion_graphEdges {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) (e : EdgeCode) :
    e ∈ graphEdges G ↔ ∃ n, e ∈ finiteEdges (H n) := by
  constructor
  · intro he
    obtain ⟨n, hn⟩ := hH.2.2 e.1.1 e.1.2 e.2 he
    exact ⟨n, (mem_finiteEdges (H n) e).mpr hn⟩
  · rintro ⟨n, hn⟩
    exact ((hH.1 n).2.1 e.1 ((mem_finiteEdges (H n) e).mp hn)).2.2.2

theorem graph_coordinate_closure {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) :
    (⨆ n, supported (𝕜 := ℝ) (finiteEdges (H n) : Set EdgeCode)).topologicalClosure =
      supported (graphEdges G) :=
  closure_iSup_supported (fun n => finiteEdges (H n)) (graphEdges G)
    (exhaustion_graphEdges hH)

theorem graph_truncate_tendsto {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) (x : Space EdgeCode ℝ) :
    Tendsto (fun n => truncate (finiteEdges (H n)) x) atTop
      (𝓝 ((supported (graphEdges G)).starProjection x)) :=
  tendsto_truncate_supported (fun n => finiteEdges (H n))
    (exhaustion_finiteEdges_monotone hH) (graphEdges G) (exhaustion_graphEdges hH) x

end Problem336.CoordinateTruncation

end

end OAI
