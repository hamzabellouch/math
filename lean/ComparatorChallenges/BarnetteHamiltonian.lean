import Mathlib

namespace OAI

namespace Barnette

universe u

/-- A topological plane drawing of a simple graph, with no crossings. -/
structure PlaneEmbedding {V : Type u} (G : SimpleGraph V) where
  point : V → ℝ × ℝ
  point_injective : Function.Injective point
  arc : ∀ (v w : V), G.Adj v w → Path (point v) (point w)
  arc_injective : ∀ (v w : V) (h : G.Adj v w),
    Function.Injective (arc v w h)
  arc_reverse : ∀ (v w : V) (h : G.Adj v w),
    arc w v h.symm = (arc v w h).symm
  arc_avoids_vertices : ∀ (v w : V) (h : G.Adj v w)
    (t : unitInterval) (z : V),
    arc v w h t = point z →
      (t = 0 ∧ z = v) ∨ (t = 1 ∧ z = w)
  interiors_disjoint : ∀ (v w x y : V) (h : G.Adj v w) (k : G.Adj x y)
    (t s : unitInterval),
    t ≠ 0 → t ≠ 1 → s ≠ 0 → s ≠ 1 →
    arc v w h t = arc x y k s →
      (v = x ∧ w = y) ∨ (v = y ∧ w = x)

/-- Planarity means existence of a crossing-free topological plane embedding. -/
def Planar {V : Type u} (G : SimpleGraph V) : Prop :=
  Nonempty (PlaneEmbedding G)

/-- Deleting any set of at most two vertices leaves a connected graph of order at least two. -/
def ThreeVertexConnected {V : Type u} [Fintype V] (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card ≤ 2 → (G.induce {v | v ∉ S}).Connected

/-- A single spanning cycle, not a possibly disconnected spanning 2-factor. -/
def HasHamiltonianCycle {V : Type u} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ v : V, ∃ p : G.Walk v v, p.IsHamiltonianCycle

/-- Cubic bipartite three-vertex-connected plane graphs have a Hamiltonian cycle. -/
def MainStatement : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 → G.IsBipartite → Planar G →
      ThreeVertexConnected G → HasHamiltonianCycle G

theorem main : MainStatement.{u} := by
  sorry

end Barnette

end OAI
