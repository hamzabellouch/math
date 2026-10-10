import OAI.Combinatorics.Crossing.DrawingDefinition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Path

namespace OAI

/-! Continuous graph drawings, proper spatial crossings, incidence, and endpoint properties. -/

section

/-!

The coordinate plane has its usual topology; every Euclidean circle below is
specified by squaredLength, not by the product norm.
-/

noncomputable section
open Set
open scoped BigOperators Classical

namespace Paper170

abbrev Plane := ℝ × ℝ

def squaredLength (x : Plane) : ℝ := x.1 ^ 2 + x.2 ^ 2

def det2 (x y : Plane) : ℝ := x.1 * y.2 - x.2 * y.1

def segmentPoint (a b : Plane) (t : ℝ) : Plane := (1 - t) • a + t • b

/-- One chosen orientation of each edge of a finite simple graph. -/
structure Graph (V E : Type) where
  src : E → V
  dst : E → V
  loopless : ∀ e, src e ≠ dst e
  simple : ∀ e f, ((src e = src f ∧ dst e = dst f) ∨
    (src e = dst f ∧ dst e = src f)) → e = f

abbrev CompleteEdge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

instance (n : ℕ) : Fintype (CompleteEdge n) := Fintype.ofFinite _

def completeGraph (n : ℕ) : Graph (Fin n) (CompleteEdge n) where
  src e := e.val.1
  dst e := e.val.2
  loopless e := ne_of_lt e.property
  simple e f h := by
    rcases h with h | h
    · exact Subtype.ext (Prod.ext h.1 h.2)
    · have he := e.property
      have hf := f.property
      rw [h.1, h.2] at he
      exact (lt_asymm he hf).elim

variable {V E : Type} (G : Graph V E)

namespace Graph

abbrev IncidentEdge (v : V) := {e : E // G.src e = v ∨ G.dst e = v}

end Graph

/-- Actual injective continuous edge arcs, with unrestricted routing. -/
structure ContinuousDrawing where
  vertex : V → Plane
  vertex_injective : Function.Injective vertex
  edge : ∀ e : E, Path (vertex (G.src e)) (vertex (G.dst e))
  edge_injective : ∀ e, Function.Injective (edge e)
  interior_avoids_vertices : ∀ e t, t ∈ Ioo (0 : unitInterval) 1 →
    ∀ v, edge e t ≠ vertex v

variable {G}

def edgeInterior (D : ContinuousDrawing G) (e : E) : Set Plane :=
  D.edge e '' Ioo (0 : unitInterval) 1

/-- A proper double crossing is locally homeomorphic to two coordinate axes. -/
structure ProperCrossing (A B : Set Plane) (x : Plane) : Prop where
  chart_exists : ∃ chart : OpenPartialHomeomorph Plane Plane,
    x ∈ chart.source ∧ chart x = (0, 0) ∧
    chart '' (chart.source ∩ A) = chart.target ∩ {y | y.2 = 0} ∧
    chart '' (chart.source ∩ B) = chart.target ∩ {y | y.1 = 0}

/-- Spatial intersection points. Different meetings of the same pair remain distinct. -/
def crossingPoints (D : ContinuousDrawing G) : Set Plane :=
  {x | ∃ e f : E, e ≠ f ∧ x ∈ edgeInterior D e ∧ x ∈ edgeInterior D f}

structure AdmissibleDrawing (G : Graph V E) extends ContinuousDrawing G where
  crossings_finite : (crossingPoints toContinuousDrawing).Finite
  crossings_proper : ∀ e f, e ≠ f → ∀ x,
    x ∈ edgeInterior toContinuousDrawing e → x ∈ edgeInterior toContinuousDrawing f →
      ProperCrossing (edgeInterior toContinuousDrawing e) (edgeInterior toContinuousDrawing f) x
  no_triples : ∀ e f g, e ≠ f → e ≠ g → f ≠ g →
    edgeInterior toContinuousDrawing e ∩ edgeInterior toContinuousDrawing f ∩
      edgeInterior toContinuousDrawing g = ∅

def crossingCount (D : AdmissibleDrawing G) : ℕ := D.crossings_finite.toFinset.card

/-- The minimum spatial crossing count over admissible drawings. -/
def ordinaryCrossingNumber (G : Graph V E) : ℕ := sInf (range (@crossingCount V E G))

/-- A finite affine parametrization of the actual path. -/
structure PolygonalParametrization {a b : Plane} (γ : Path a b) where
  pieces : ℕ
  positive : 0 < pieces
  knot : Fin (pieces + 1) → unitInterval
  increasing : StrictMono knot
  first : knot 0 = 0
  last : knot (Fin.last pieces) = 1
  affine : ∀ i : Fin pieces, ∀ t : unitInterval,
    knot i.castSucc ≤ t → t ≤ knot i.succ →
    γ t = segmentPoint (γ (knot i.castSucc)) (γ (knot i.succ))
      (((t : ℝ) - knot i.castSucc) / ((knot i.succ : ℝ) - knot i.castSucc))

def PolygonalParametrization.vertices {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) (i : ℕ) : Plane :=
  γ (P.knot ⟨min i P.pieces, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)

/-- A convenient subdivision of a normalized drawing. Avoiding subdivision
knots at crossings is additional presentation data, obtained by the normalization theorem. -/
structure NormalizedDrawing (G : Graph V E) extends AdmissibleDrawing G where
  polygonal : ∀ e, PolygonalParametrization (edge e)
  no_adjacent : ∀ e f, e ≠ f →
    (G.src e = G.src f ∨ G.src e = G.dst f ∨ G.dst e = G.src f ∨ G.dst e = G.dst f) →
    Disjoint (edgeInterior toContinuousDrawing e) (edgeInterior toContinuousDrawing f)
  crossings_not_knots : ∀ e (i : Fin ((polygonal e).pieces + 1)),
    edge e ((polygonal e).knot i) ∉ crossingPoints toContinuousDrawing

/-- Directed open-segment intersection, with the ordinary determinant sign. -/
def segmentIntersection (a b c d : Plane) : ℝ :=
  if ∃ s ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Ioo (0 : ℝ) 1,
      segmentPoint a b s = segmentPoint c d t then
    if 0 < det2 (b - a) (d - c) then 1
    else if det2 (b - a) (d - c) < 0 then -1 else 0
  else 0

def interiorIntersection (N : NormalizedDrawing G) (e f : E) : ℝ :=
  if e = f then 0 else
    ∑ i ∈ Finset.range (N.polygonal e).pieces,
      ∑ j ∈ Finset.range (N.polygonal f).pieces,
        segmentIntersection ((N.polygonal e).vertices i) ((N.polygonal e).vertices (i + 1))
          ((N.polygonal f).vertices j) ((N.polygonal f).vertices (j + 1))

def outwardSpoke (N : NormalizedDrawing G) (v : V) (e : E) : Plane :=
  if G.src e = v then (N.polygonal e).vertices 1 - (N.polygonal e).vertices 0
  else (N.polygonal e).vertices ((N.polygonal e).pieces - 1) -
    (N.polygonal e).vertices (N.polygonal e).pieces

def spokeAngle (cut : ℝ) (a : Plane) : ℝ :=
  Complex.arg (Complex.exp (-(cut : ℂ) * Complex.I) * (⟨a.1, a.2⟩ : ℂ))

/-- The linear local orders are witnessed by the actual counterclockwise angles,
with a cut in a gap. No intersection identity is part of this data. -/
structure SpokeOrders (N : NormalizedDrawing G) where
  cut : V → ℝ
  order : ∀ v, LinearOrder (G.IncidentEdge v)
  cut_avoids : ∀ v (e : G.IncidentEdge v), spokeAngle (cut v) (outwardSpoke N v e.val) ≠ Real.pi
  compatible : ∀ v (e f : G.IncidentEdge v),
    @LT.lt _ (order v).toLT e f ↔
      spokeAngle (cut v) (outwardSpoke N v e.val) <
        spokeAngle (cut v) (outwardSpoke N v f.val)

def endpointSign (G : Graph V E) (v : V) (e : E) : ℝ :=
  if G.src e = v then 1 else if G.dst e = v then -1 else 0

def spokeComparison {N : NormalizedDrawing G} (O : SpokeOrders N) (v : V) (e f : E) : ℝ :=
  if he : G.src e = v ∨ G.dst e = v then if hf : G.src f = v ∨ G.dst f = v then
    if @LT.lt _ (O.order v).toLT ⟨e, he⟩ ⟨f, hf⟩ then 1
    else if @LT.lt _ (O.order v).toLT ⟨f, hf⟩ ⟨e, he⟩ then -1 else 0
  else 0 else 0

variable [Fintype V] [Fintype E]

def cycleIntersection {N : NormalizedDrawing G} (O : SpokeOrders N) (e f : E) : ℝ :=
  interiorIntersection N e f + (1 / 2 : ℝ) *
    ∑ v, endpointSign G v e * endpointSign G v f * spokeComparison O v e f

def edgePairing (J : E → E → ℝ) (z z' : E → ℝ) : ℝ :=
  ∑ e, ∑ f, z e * z' f * J e f

def boundary (G : Graph V E) (z : E → ℝ) (v : V) : ℝ :=
  ∑ e, z e * ((if G.dst e = v then 1 else 0) - (if G.src e = v then 1 else 0))

def completeEdgeVector {n : ℕ} (i p : Fin n) : CompleteEdge n → ℝ :=
  fun e => if e.val.1 = i ∧ e.val.2 = p then 1
    else if e.val.1 = p ∧ e.val.2 = i then -1 else 0

def rawCycleIntersection {n : ℕ} {N : NormalizedDrawing (completeGraph n)}
    (O : SpokeOrders N) (i p k q : Fin n) : ℝ :=
  edgePairing (cycleIntersection O) (completeEdgeVector i p) (completeEdgeVector k q)

/-- A simple combinatorial cycle with a chosen direction of traversal. -/
structure SimpleCycle (G : Graph V E) where
  length : ℕ
  three_le : 3 ≤ length
  vertex : Fin length → V
  vertex_injective : Function.Injective vertex
  edge : Fin length → E
  follows : ∀ i,
    let j : Fin length := ⟨(i.val + 1) % length,
      Nat.mod_lt _ (lt_of_lt_of_le (by decide : 0 < 3) three_le)⟩
    (G.src (edge i) = vertex i ∧ G.dst (edge i) = vertex j) ∨
      (G.dst (edge i) = vertex i ∧ G.src (edge i) = vertex j)

def SimpleCycle.edgeChain (C : SimpleCycle G) : E → ℝ :=
  fun e => ∑ i, if C.edge i = e then (if G.src e = C.vertex i then 1 else -1) else 0

def polygonIntersection (v w : ℕ → Plane) (n m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
    segmentIntersection (v i) (v (i + 1)) (w j) (w (j + 1))

/-- Only proper interior meetings between the two polygonal walks. -/
structure TransversePolygons (v w : ℕ → Plane) (n m : ℕ) : Prop where
  left_vertices_avoid : ∀ i, i ≤ n → ∀ j, j < m → ∀ t ∈ Icc (0 : ℝ) 1,
    v i ≠ segmentPoint (w j) (w (j + 1)) t
  right_vertices_avoid : ∀ j, j ≤ m → ∀ i, i < n → ∀ t ∈ Icc (0 : ℝ) 1,
    w j ≠ segmentPoint (v i) (v (i + 1)) t
  transverse : ∀ i, i < n → ∀ j, j < m →
    (∃ s ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Ioo (0 : ℝ) 1,
      segmentPoint (v i) (v (i + 1)) s = segmentPoint (w j) (w (j + 1)) t) →
    det2 (v (i + 1) - v i) (w (j + 1) - w j) ≠ 0

def circleComparison (cut : ℝ) (a b : Plane) : ℝ :=
  if spokeAngle cut a < spokeAngle cut b then 1
  else if spokeAngle cut b < spokeAngle cut a then -1 else 0

def inversion (z : Plane) : Plane := (z.1 / squaredLength z, z.2 / squaredLength z)

end Paper170

end
end

section

/-! Converting actual nonvertex trace contacts to the exact crossing-point definition. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem edgeInterior_subset_range (D : Paper170.ContinuousDrawing graph) (e : Edge) :
    Paper170.edgeInterior D e ⊆ Set.range (D.edge e) := by
  rintro x ⟨t,_,he⟩
  exact ⟨t,he⟩

theorem edgeInterior_of_range_not_vertices (D : Paper170.ContinuousDrawing graph) (e : Edge)
    (x : Plane) (hx : x ∈ Set.range (D.edge e)) (hvertex : ∀ j, x ≠ D.vertex j) :
    x ∈ Paper170.edgeInterior D e := by
  obtain ⟨t,he⟩ := hx
  have ht0 : t ≠ 0 := by
    intro ht
    subst t
    exact hvertex _ (he.symm.trans (D.edge e).source)
  have ht1 : t ≠ 1 := by
    intro ht
    subst t
    exact hvertex _ (he.symm.trans (D.edge e).target)
  exact ⟨t,⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩,he⟩

theorem edgeInterior_not_vertex (D : Paper170.ContinuousDrawing graph) (e : Edge)
    (x : Plane) (hx : x ∈ Paper170.edgeInterior D e) (j : Vertex) : x ≠ D.vertex j := by
  obtain ⟨t,ht,he⟩ := hx
  exact fun hj => D.interior_avoids_vertices e t ht j (he.trans hj)

theorem crossing_of_ranges_not_vertices (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (hef : e ≠ f) (x : Plane) (he : x ∈ Set.range (D.edge e)) (hf : x ∈ Set.range (D.edge f))
    (hv : ∀ j, x ≠ D.vertex j) : x ∈ Paper170.crossingPoints D :=
  ⟨e,f,hef,edgeInterior_of_range_not_vertices D e x he hv,edgeInterior_of_range_not_vertices D f x hf hv⟩

end Paper170Geometry

end
end

section

namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

theorem drawing_edge_vertex_parameter (D : Paper170.ContinuousDrawing graph) (e : Edge)
    (t : unitInterval) (v : Vertex) (he : D.edge e t=D.vertex v) :
    (t=0 ∧ v=(graph.src e)) ∨ (t=1 ∧ v=(graph.dst e)) := by
  by_cases ht0 : t=0
  · subst t
    exact Or.inl ⟨rfl,(D.vertex_injective ((D.edge e).source.symm.trans he)).symm⟩
  by_cases ht1 : t=1
  · subst t
    exact Or.inr ⟨rfl,(D.vertex_injective ((D.edge e).target.symm.trans he)).symm⟩
  exact False.elim (D.interior_avoids_vertices e t
    ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩ v he)

end Paper170Geometry

end

section

/-! A weaker INPUT for normalization: actual simple routes with finite contacts and no triples.
The endpoint's Paper170.AdmissibleDrawing and MainTarget definitions are unchanged. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

structure FiniteIntersectionDrawing (graph : Paper170.Graph Vertex Edge) extends Paper170.ContinuousDrawing graph where
  crossings_finite : (Paper170.crossingPoints toContinuousDrawing).Finite
  no_triples : ∀ e f g, e ≠ f → e ≠ g → f ≠ g →
    Paper170.edgeInterior toContinuousDrawing e ∩ Paper170.edgeInterior toContinuousDrawing f ∩
      Paper170.edgeInterior toContinuousDrawing g = ∅

abbrev toFiniteIntersectionDrawing  (D : Paper170.AdmissibleDrawing graph) :
    FiniteIntersectionDrawing graph where
  toContinuousDrawing := D.toContinuousDrawing
  crossings_finite := D.crossings_finite
  no_triples := D.no_triples

instance admissibleToFiniteIntersectionDrawing  :
    CoeOut (Paper170.AdmissibleDrawing graph) (FiniteIntersectionDrawing graph) :=
  ⟨toFiniteIntersectionDrawing⟩

def finiteCrossingCount  (D : FiniteIntersectionDrawing graph) : ℕ :=
  D.crossings_finite.toFinset.card

theorem finiteCrossingCount_of_admissible  (D : Paper170.AdmissibleDrawing graph) :
    finiteCrossingCount (D : FiniteIntersectionDrawing graph)=Paper170.crossingCount D := rfl

theorem finiteCrossingCount_eq_ncard  (D : FiniteIntersectionDrawing graph) :
    finiteCrossingCount D=(Paper170.crossingPoints D.toContinuousDrawing).ncard :=
  (Set.ncard_eq_toFinset_card _ D.crossings_finite).symm

end Paper170Geometry

namespace Paper170.AdmissibleDrawing

abbrev toFiniteIntersectionDrawing {V E : Type} {G : Graph V E} (D : AdmissibleDrawing G) :
    Paper170Geometry.FiniteIntersectionDrawing G := Paper170Geometry.toFiniteIntersectionDrawing D

end Paper170.AdmissibleDrawing

end
end

section

/-! Finite point incidence for actual drawings, retaining repeated pair crossings. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
open scoped BigOperators Classical
/-- A minimum exists once an actual admissible drawing has been constructed.
This is the well-ordering step; construction of a drawing remains a separate obligation. -/
theorem crossingCount_attainment (D₀ : Paper170.AdmissibleDrawing graph) :
    ∃ D : Paper170.AdmissibleDrawing graph, Paper170.crossingCount D = Paper170.ordinaryCrossingNumber graph := by
  exact csInf_mem (show (Set.range (@Paper170.crossingCount Vertex Edge graph)).Nonempty from
    ⟨Paper170.crossingCount D₀, D₀, rfl⟩)

theorem ordinaryCrossingNumber_le_count (D : Paper170.AdmissibleDrawing graph) :
    Paper170.ordinaryCrossingNumber graph ≤ Paper170.crossingCount D :=
  csInf_le' ⟨D, rfl⟩

theorem crossing_incident_iff (D : Paper170.AdmissibleDrawing graph) (x : Plane)
    (e f : Edge) (hef : e ≠ f)
    (he : x ∈ Paper170.edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ Paper170.edgeInterior D.toContinuousDrawing f) (g : Edge) :
    x ∈ Paper170.edgeInterior D.toContinuousDrawing g ↔ g = e ∨ g = f := by
  constructor
  · intro hg
    by_contra hh
    have hge : e ≠ g := by tauto
    have hgf : f ≠ g := by tauto
    have hmem : x ∈ Paper170.edgeInterior D.toContinuousDrawing e ∩ Paper170.edgeInterior D.toContinuousDrawing f ∩
        Paper170.edgeInterior D.toContinuousDrawing g := ⟨⟨he,hf⟩,hg⟩
    rw [D.no_triples e f g hef hge hgf] at hmem
    exact hmem
  · rintro (rfl | rfl) <;> assumption

/-- Every spatial crossing has exactly two incident edges; no bound is imposed
on the number of points common to that edge pair. -/
theorem crossing_two_edges (D : Paper170.AdmissibleDrawing graph) (x : Plane)
    (hx : x ∈ Paper170.crossingPoints D.toContinuousDrawing) :
    ∃ e f : Edge, e ≠ f ∧
      ∀ g, x ∈ Paper170.edgeInterior D.toContinuousDrawing g ↔ g = e ∨ g = f := by
  obtain ⟨e,f,hef,he,hf⟩ := hx
  exact ⟨e,f,hef,crossing_incident_iff D x e f hef he hf⟩

/-- The actual finite set of crossing points for a specified ordered edge pair. -/
def pairCrossings (D : Paper170.AdmissibleDrawing graph) (e f : Edge) : Finset Plane :=
  D.crossings_finite.toFinset.filter (fun x => e ≠ f ∧
    x ∈ Paper170.edgeInterior D.toContinuousDrawing e ∧ x ∈ Paper170.edgeInterior D.toContinuousDrawing f)

theorem pairCrossings_self (D : Paper170.AdmissibleDrawing graph) (e : Edge) :
    pairCrossings D e e = ∅ := by
  simp [pairCrossings]

theorem pairCrossings_comm (D : Paper170.AdmissibleDrawing graph) (e f : Edge) :
    pairCrossings D e f = pairCrossings D f e := by
  ext x
  simp only [pairCrossings, Finset.mem_filter]
  tauto

variable [Fintype Edge]

/-- Each crossing point contributes two ordered edge pairs. -/
theorem crossing_ordered_incidence (D : Paper170.AdmissibleDrawing graph) (x : Plane)
    (hx : x ∈ Paper170.crossingPoints D.toContinuousDrawing) :
    (∑ e : Edge, ∑ f : Edge,
      if e ≠ f ∧ x ∈ Paper170.edgeInterior D.toContinuousDrawing e ∧
        x ∈ Paper170.edgeInterior D.toContinuousDrawing f then (1 : ℕ) else 0) = 2 := by
  classical
  obtain ⟨e,f,hef,hinc⟩ := crossing_two_edges D x hx
  simp_rw [hinc]
  have hp : ∀ a b : Edge,
      (a ≠ b ∧ (a = e ∨ a = f) ∧ (b = e ∨ b = f)) ↔
        ((a = e ∧ b = f) ∨ (a = f ∧ b = e)) := by
    intro a b
    constructor
    · rintro ⟨hab, rfl | rfl, rfl | rfl⟩ <;> tauto
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> tauto
  simp_rw [hp]
  have hi : ∀ a b : Edge,
      (if (a = e ∧ b = f) ∨ (a = f ∧ b = e) then (1 : ℕ) else 0) =
        (if a = e ∧ b = f then 1 else 0) + (if a = f ∧ b = e then 1 else 0) := by
    intro a b
    split_ifs <;> simp_all
  simp_rw [hi, Finset.sum_add_distrib]
  simp [ite_and]

/-- Sum over ordered edge pairs equals twice the number of spatial crossing points. -/
theorem sum_pairCrossings_card (D : Paper170.AdmissibleDrawing graph) :
    (∑ e : Edge, ∑ f : Edge, (pairCrossings D e f).card) =
      2 * Paper170.crossingCount D := by
  classical
  simp only [pairCrossings, Finset.card_filter]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext f; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have he : ∀ x ∈ D.crossings_finite.toFinset,
      (∑ f : Edge, ∑ e : Edge,
        if e ≠ f ∧ x ∈ Paper170.edgeInterior D.toContinuousDrawing e ∧
          x ∈ Paper170.edgeInterior D.toContinuousDrawing f then (1 : ℕ) else 0) = 2 := by
    intro x hx
    rw [Finset.sum_comm]
    exact crossing_ordered_incidence D x (by simpa using hx)
  simp_rw [Finset.sum_congr rfl he]
  simp [Paper170.crossingCount, Nat.mul_comm]

end Paper170Geometry

end
end

end OAI
