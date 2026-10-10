import Mathlib.Topology.Path
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

namespace OAI

noncomputable section

namespace Zarankiewicz

def axisPairs (r : ℕ) : ℕ := (r/2) * ((r-1)/2)


abbrev Plane := ℝ × ℝ
abbrev BipartiteVertex (m n : ℕ) := Fin m ⊕ Fin n
abbrev BipartiteEdge (m n : ℕ) := Fin m × Fin n

structure ContinuousDrawing (m n : ℕ) where
  vertex : BipartiteVertex m n → Plane
  vertex_injective : Function.Injective vertex
  edge : ∀ e : BipartiteEdge m n, Path (vertex (.inl e.1)) (vertex (.inr e.2))
  edge_injective : ∀ e, Function.Injective (edge e)
  interior_avoids_vertices : ∀ e t, t ∈ Set.Ioo (0 : unitInterval) 1 →
    ∀ v, edge e t ≠ vertex v

def edgeInterior {m n : ℕ} (D : ContinuousDrawing m n) (e : BipartiteEdge m n) : Set Plane :=
  D.edge e '' Set.Ioo (0 : unitInterval) 1

def ProperCrossing (A B : Set Plane) (x : Plane) : Prop :=
  ∃ chart : OpenPartialHomeomorph Plane Plane,
    x ∈ chart.source ∧ chart x = (0,0) ∧
    chart '' (chart.source ∩ A) = chart.target ∩ {y | y.2 = 0} ∧
    chart '' (chart.source ∩ B) = chart.target ∩ {y | y.1 = 0}

def crossingPoints {m n : ℕ} (D : ContinuousDrawing m n) : Set Plane :=
  {x | ∃ e f : BipartiteEdge m n, e ≠ f ∧ x ∈ edgeInterior D e ∧ x ∈ edgeInterior D f}

structure AdmissibleDrawing (m n : ℕ) extends ContinuousDrawing m n where
  crossings_finite : (crossingPoints toContinuousDrawing).Finite
  crossings_proper : ∀ e f, e ≠ f → ∀ x,
    x ∈ edgeInterior toContinuousDrawing e → x ∈ edgeInterior toContinuousDrawing f →
    ProperCrossing (edgeInterior toContinuousDrawing e) (edgeInterior toContinuousDrawing f) x
  no_triples : ∀ e f g, e ≠ f → e ≠ g → f ≠ g →
    edgeInterior toContinuousDrawing e ∩ edgeInterior toContinuousDrawing f ∩
      edgeInterior toContinuousDrawing g = ∅

def crossingCount {m n : ℕ} (D : AdmissibleDrawing m n) : ℕ := D.crossings_finite.toFinset.card

def MainTarget : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    (∃ D : AdmissibleDrawing m n, crossingCount D = axisPairs m * axisPairs n) ∧
    (∀ D : AdmissibleDrawing m n, axisPairs m * axisPairs n ≤ crossingCount D)

theorem mainTarget_proof : MainTarget := by
  sorry

end Zarankiewicz

end

end OAI
