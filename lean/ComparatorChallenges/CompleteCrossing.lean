import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Path

namespace OAI

noncomputable section

namespace Paper170

abbrev Plane := ℝ × ℝ

structure Graph (Vertex Edge : Type) where
  src : Edge → Vertex
  dst : Edge → Vertex
  loopless : ∀ edge, src edge ≠ dst edge
  simple : ∀ edge other, ((src edge = src other ∧ dst edge = dst other) ∨
    (src edge = dst other ∧ dst edge = src other)) → edge = other

abbrev CompleteEdge (order : ℕ) := {pair : Fin order × Fin order // pair.1 < pair.2}

def completeGraph (order : ℕ) : Graph (Fin order) (CompleteEdge order) where
  src edge := edge.val.1
  dst edge := edge.val.2
  loopless edge := ne_of_lt edge.property
  simple edge other same := by
    rcases same with same | reversed
    · exact Subtype.ext (Prod.ext same.1 same.2)
    · have increasing := edge.property
      have other_increasing := other.property
      rw [reversed.1, reversed.2] at increasing
      exact (lt_asymm increasing other_increasing).elim

variable {Vertex Edge : Type}

structure ContinuousDrawing (graph : Graph Vertex Edge) where
  vertex : Vertex → Plane
  vertex_injective : Function.Injective vertex
  edge : ∀ edge : Edge, Path (vertex (graph.src edge)) (vertex (graph.dst edge))
  edge_injective : ∀ selected, Function.Injective (edge selected)
  interior_avoids_vertices : ∀ selected time, time ∈ Set.Ioo (0 : unitInterval) 1 →
    ∀ other, edge selected time ≠ vertex other

variable {graph : Graph Vertex Edge}

def edgeInterior (drawing : ContinuousDrawing graph) (edge : Edge) : Set Plane :=
  drawing.edge edge '' Set.Ioo (0 : unitInterval) 1

structure ProperCrossing (first second : Set Plane) (point : Plane) : Prop where
  chart_exists : ∃ chart : OpenPartialHomeomorph Plane Plane,
    point ∈ chart.source ∧ chart point = (0, 0) ∧
    chart '' (chart.source ∩ first) = chart.target ∩ {image | image.2 = 0} ∧
    chart '' (chart.source ∩ second) = chart.target ∩ {image | image.1 = 0}

def crossingPoints (drawing : ContinuousDrawing graph) : Set Plane :=
  {point | ∃ edge other : Edge, edge ≠ other ∧
    point ∈ edgeInterior drawing edge ∧ point ∈ edgeInterior drawing other}

structure AdmissibleDrawing (graph : Graph Vertex Edge) extends ContinuousDrawing graph where
  crossings_finite : (crossingPoints toContinuousDrawing).Finite
  crossings_proper : ∀ edge other, edge ≠ other → ∀ point,
    point ∈ edgeInterior toContinuousDrawing edge →
    point ∈ edgeInterior toContinuousDrawing other →
    ProperCrossing (edgeInterior toContinuousDrawing edge)
      (edgeInterior toContinuousDrawing other) point
  no_triples : ∀ first second third, first ≠ second → first ≠ third → second ≠ third →
    edgeInterior toContinuousDrawing first ∩ edgeInterior toContinuousDrawing second ∩
      edgeInterior toContinuousDrawing third = ∅

def crossingCount (drawing : AdmissibleDrawing graph) : ℕ :=
  drawing.crossings_finite.toFinset.card

def ordinaryCrossingNumber (graph : Graph Vertex Edge) : ℕ :=
  sInf (Set.range (@crossingCount Vertex Edge graph))

def hill (order : ℕ) : ℕ :=
  (order / 2 * ((order - 1) / 2) * ((order - 2) / 2) * ((order - 3) / 2)) / 4

theorem complete_graph_crossing_number (order : ℕ) (at_least_three : 3 ≤ order) :
    ordinaryCrossingNumber (completeGraph order) = hill order := by
  sorry

end Paper170

end

end OAI
