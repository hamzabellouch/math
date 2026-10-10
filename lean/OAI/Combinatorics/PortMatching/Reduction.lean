import OAI.Combinatorics.PortMatching.Extension
import OAI.Combinatorics.PortMatching.Decoding
import OAI.Combinatorics.PortMatching.Size

namespace OAI

/-! Perfect-matching-preserving port-path degree reduction for finite simple graphs. -/

noncomputable section
namespace Matching205
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem perfectMatching_forward (M : G.Subgraph) (hM : M.IsPerfectMatching) :
    ∃ N : (graph G).Subgraph, N.IsPerfectMatching :=
  ⟨Forward.extend G M hM, Forward.extend_perfect G M hM⟩

theorem perfectMatching_reverse (hpos : ∀ v : V, 0 < G.degree v)
    (N : (graph G).Subgraph) (hN : N.IsPerfectMatching) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  have ha : ∀ v : V, 0 < arity G v := by
    intro v
    simpa only [arity, SimpleGraph.card_neighborSet_eq_degree] using hpos v
  exact ⟨decode G N, decode_isPerfectMatching G ha hN⟩

theorem perfectMatching_iff (hpos : ∀ v : V, 0 < G.degree v) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∃ N : (graph G).Subgraph, N.IsPerfectMatching := by
  constructor
  · rintro ⟨M, hM⟩
    exact perfectMatching_forward G M hM
  · rintro ⟨N, hN⟩
    exact perfectMatching_reverse G hpos N hN

theorem simpleGraphReduction (hpos : ∀ v : V, 0 < G.degree v) :
    ((∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∃ N : (graph G).Subgraph, N.IsPerfectMatching) ∧
    (∀ x : Vertex G, (graph G).degree x ≤ 3) ∧
    Fintype.card (Vertex G) = 4 * G.edgeFinset.card - Fintype.card V :=
  ⟨perfectMatching_iff G hpos, graph_degree_le_three G, card_vertex G hpos⟩

end Matching205

end

end OAI
