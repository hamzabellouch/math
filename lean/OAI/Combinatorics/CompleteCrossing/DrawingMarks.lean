import OAI.Combinatorics.CompleteCrossing.Drawing
import OAI.Combinatorics.Crossing.AffineSubdivisionRefinement
import OAI.Combinatorics.Crossing.DrawingEdgeWalkTrace
import OAI.Combinatorics.Crossing.EmbeddedGraphPaths
import OAI.Combinatorics.Crossing.GraphSequenceWalk
import OAI.Combinatorics.Crossing.OrderedAffineSubdivision
import OAI.Combinatorics.Crossing.OrderedKnotCover
import OAI.Combinatorics.Crossing.PathSubarc
import OAI.Combinatorics.Crossing.SortedMarkedParameters
import OAI.Combinatorics.Crossing.SubdivisionSegments

namespace OAI

/-! Marked subdivision parameters, incidence graphs, and edge walks. -/

section

/-! The actual finite marks and marked parameters of a continuous drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
def drawingMarks (D : FiniteIntersectionDrawing graph) : Set Plane :=
  Set.range D.vertex ∪ Paper170.crossingPoints D.toContinuousDrawing

theorem drawingMarks_finite [Fintype Vertex] (D : FiniteIntersectionDrawing graph) : (drawingMarks D).Finite :=
  (Set.finite_range D.vertex).union D.crossings_finite

theorem crossing_not_vertex (D : FiniteIntersectionDrawing graph) (x : Plane)
    (hx : x ∈ Paper170.crossingPoints D.toContinuousDrawing) (v : Vertex) : x ≠ D.vertex v := by
  obtain ⟨e,f,hef,⟨t,ht,he⟩,hf⟩ := hx
  intro hh
  exact D.interior_avoids_vertices e t ht v (he.trans hh)

theorem marked_parameters_finite [Fintype Vertex] (D : FiniteIntersectionDrawing graph) (e : Edge) :
    ((D.edge e) ⁻¹' drawingMarks D).Finite :=
  Set.Finite.preimage (D.edge_injective e).injOn (drawingMarks_finite D)

theorem marked_parameter_zero (D : FiniteIntersectionDrawing graph) (e : Edge) :
    (0 : unitInterval) ∈ (D.edge e) ⁻¹' drawingMarks D := by
  exact Or.inl ⟨graph.src e,(D.edge e).source.symm⟩

theorem marked_parameter_one (D : FiniteIntersectionDrawing graph) (e : Edge) :
    (1 : unitInterval) ∈ (D.edge e) ⁻¹' drawingMarks D := by
  exact Or.inl ⟨graph.dst e,(D.edge e).target.symm⟩

theorem unmarked_edge_point_interior (D : FiniteIntersectionDrawing graph) (e : Edge)
    (t : unitInterval) (ht : D.edge e t ∉ drawingMarks D) : t ∈ Set.Ioo (0 : unitInterval) 1 := by
  have ht0 : t ≠ 0 := by
    intro he
    subst t
    exact ht (marked_parameter_zero D e)
  have ht1 : t ≠ 1 := by
    intro he
    subst t
    exact ht (marked_parameter_one D e)
  exact ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩

theorem unmarked_intersection_same_edge (D : FiniteIntersectionDrawing graph)
    (e f : Edge) (s t : unitInterval)
    (he : D.edge e s=D.edge f t) (hs : D.edge e s ∉ drawingMarks D) : e=f := by
  by_contra hef
  have hsi := unmarked_edge_point_interior D e s hs
  have hti := unmarked_edge_point_interior D f t (he ▸ hs)
  exact hs (Or.inr ⟨e,f,hef,⟨s,hsi,rfl⟩,⟨t,hti,he.symm⟩⟩)

end Paper170Geometry

end
end

section

/-! Increasing enumeration of the actual marked parameters, with both endpoints. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem exists_sorted_drawing_parameters [Fintype Vertex] (D : FiniteIntersectionDrawing graph)
    (e : Edge) :
    ∃ k : ℕ, 0 < k ∧ ∃ t : Fin (k+1) → unitInterval,
      StrictMono t ∧ t 0=0 ∧ t (Fin.last k)=1 ∧
      Set.range t=(D.edge e) ⁻¹' drawingMarks D := by
  obtain ⟨k,hk,t,ht,h0,h1,hR⟩ := exists_sorted_unitInterval_finset (marked_parameters_finite D e).toFinset
    (by simpa using marked_parameter_zero D e) (by simpa using marked_parameter_one D e)
  exact ⟨k,hk,t,ht,h0,h1,by simpa using hR⟩

end Paper170Geometry

end
end

section

/-! Refine an actual polygonal path at any prescribed finite set of parameters. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem exists_marked_polygonal_subdivision [Fintype Vertex] (D : Paper170.AdmissibleDrawing graph)
    (hpoly : ∀ e, HasFiniteAffineCover (D.edge e)) :
    ∃ P : ∀ e, PolygonalParametrization (D.edge e),
      ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot := by
  classical
  have hex (e : Edge) := (hpoly e).refine (marked_parameters_finite D.toFiniteIntersectionDrawing e).toFinset
  choose P hP using hex
  exact ⟨P,fun e t ht => hP e (by simpa using ht)⟩

end Paper170Geometry

end
end

section

/-! Actual subdivision segments, parameter witnesses, and marked-point endpoints. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem subdivision_mark_endpoint (D : Paper170.AdmissibleDrawing graph)
    (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (e : Edge) (i : Fin (P e).pieces) (x : Plane)
    (hx : x ∈ (P e).pieceTrace i) (hm : x ∈ drawingMarks D.toFiniteIntersectionDrawing) :
    x=D.edge e ((P e).knot i.castSucc) ∨ x=D.edge e ((P e).knot i.succ) := by
  obtain ⟨t,ht⟩ := (P e).pieceTrace_subset_range i hx
  obtain ⟨j,hj⟩ := hmark e t (ht.symm ▸ hm)
  have he : D.edge e ((P e).knot j)=x := (congrArg (D.edge e) hj).trans ht
  have hh := (P e).pieceTrace_knot_endpoint (D.edge_injective e) i j (he.symm ▸ hx)
  simpa only [he] using hh

end Paper170Geometry

end
end

section

/-! Refined segments of the actual drawing meet only at common subdivision endpoints. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem drawing_curve_meeting_mark (D : Paper170.AdmissibleDrawing graph) (e f : Edge)
    (hef : e ≠ f) (x : Plane) (hx : x ∈ Set.range (D.edge e)) (hy : x ∈ Set.range (D.edge f)) :
    x ∈ drawingMarks D.toFiniteIntersectionDrawing := by
  obtain ⟨s,hs⟩ := hx
  obtain ⟨t,ht⟩ := hy
  by_cases hs0 : s=0
  · subst s
    exact Or.inl ⟨(graph.src e),by simpa using hs⟩
  by_cases hs1 : s=1
  · subst s
    exact Or.inl ⟨(graph.dst e),by simpa using hs⟩
  by_cases ht0 : t=0
  · subst t
    exact Or.inl ⟨(graph.src f),by simpa using ht⟩
  by_cases ht1 : t=1
  · subst t
    exact Or.inl ⟨(graph.dst f),by simpa using ht⟩
  exact Or.inr ⟨e,f,hef,
    ⟨s,⟨lt_of_le_of_ne (show 0 ≤ s from s.property.1) (Ne.symm hs0),
      lt_of_le_of_ne (show s ≤ 1 from s.property.2) hs1⟩,hs⟩,
    ⟨t,⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩,ht⟩⟩

abbrev DrawingPiece {D : Paper170.AdmissibleDrawing graph} (P : ∀ e, PolygonalParametrization (D.edge e)) :=
  (e : Edge) × Fin (P e).pieces

def drawingPieceStart {D : Paper170.AdmissibleDrawing graph} (P : ∀ e, PolygonalParametrization (D.edge e))
    (i : DrawingPiece P) : Plane := D.edge i.1 ((P i.1).knot i.2.castSucc)

def drawingPieceEnd {D : Paper170.AdmissibleDrawing graph} (P : ∀ e, PolygonalParametrization (D.edge e))
    (i : DrawingPiece P) : Plane := D.edge i.1 ((P i.1).knot i.2.succ)

theorem drawingPiece_endpoints_ne {D : Paper170.AdmissibleDrawing graph}
    (P : ∀ e, PolygonalParametrization (D.edge e)) (i : DrawingPiece P) :
    drawingPieceStart P i ≠ drawingPieceEnd P i := by
  intro he
  have hh := D.edge_injective i.1 he
  exact ((P i.1).increasing (show i.2.castSucc < i.2.succ by change i.2.val < i.2.val+1; omega)).ne hh

theorem drawing_pieces_meeting_endpoints (D : Paper170.AdmissibleDrawing graph)
    (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (p q : DrawingPiece P) (hpq : p ≠ q) (x : Plane)
    (hx : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p))
    (hy : x ∈ segment ℝ (drawingPieceStart P q) (drawingPieceEnd P q)) :
    (x=drawingPieceStart P p ∨ x=drawingPieceEnd P p) ∧
      (x=drawingPieceStart P q ∨ x=drawingPieceEnd P q) := by
  rcases p with ⟨e,i⟩
  rcases q with ⟨f,j⟩
  by_cases hef : e=f
  · subst f
    have hij : i ≠ j := fun he => hpq (by subst j; rfl)
    exact ⟨(P e).pieceTrace_other_piece_endpoint (D.edge_injective e) i j hij x hx hy,
      (P e).pieceTrace_other_piece_endpoint (D.edge_injective e) j i (Ne.symm hij) x hy hx⟩
  · have hm := drawing_curve_meeting_mark D e f hef x
      ((P e).pieceTrace_subset_range i hx) ((P f).pieceTrace_subset_range j hy)
    exact ⟨subdivision_mark_endpoint D P hmark e i x hx hm,
      subdivision_mark_endpoint D P hmark f j x hy hm⟩

end Paper170Geometry

end
end

section

/-! The actual straight embedded graph formed by refined drawing segments. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D : Paper170.AdmissibleDrawing graph}

def drawingSubdivisionGraph (P : ∀ e, PolygonalParametrization (D.edge e)) : SimpleGraph Plane where
  Adj := fun a b => a ≠ b ∧ ∃ p : DrawingPiece P,
    (a=drawingPieceStart P p ∧ b=drawingPieceEnd P p) ∨
      (a=drawingPieceEnd P p ∧ b=drawingPieceStart P p)
  symm := ⟨by
    rintro a b ⟨hab,p,hp⟩
    refine ⟨Ne.symm hab,p,?_⟩
    rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inr ⟨hb,ha⟩
    · exact Or.inl ⟨hb,ha⟩⟩
  loopless := ⟨by rintro a ⟨ha,_⟩; exact ha rfl⟩

theorem drawingSubdivisionGraph_piece_adj (P : ∀ e, PolygonalParametrization (D.edge e))
    (p : DrawingPiece P) :
    (drawingSubdivisionGraph P).Adj (drawingPieceStart P p) (drawingPieceEnd P p) :=
  ⟨drawingPiece_endpoints_ne P p,p,Or.inl ⟨rfl,rfl⟩⟩

theorem common_endpoint_alternatives (a b c d x : Plane) (hab : x=a ∨ x=b) (hcd : x=c ∨ x=d) :
    (a=c ∧ x=a) ∨ (a=d ∧ x=a) ∨ (b=c ∧ x=b) ∨ (b=d ∧ x=b) := by
  rcases hab with ha | hb <;> rcases hcd with hc | hd
  · exact Or.inl ⟨ha.symm.trans hc,ha⟩
  · exact Or.inr (Or.inl ⟨ha.symm.trans hd,ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hb.symm.trans hc,hb⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hb.symm.trans hd,hb⟩))

theorem drawingSubdivisionGraph_embedding (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot) :
    StraightEdgeEmbedding (drawingSubdivisionGraph P) id := by
  refine ⟨Function.injective_id,?_⟩
  rintro a b c d ⟨hab,p,hp⟩ ⟨hcd,q,hq⟩ x hx hy
  by_cases hpq : p=q
  · subst q
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
    · exact Or.inl ⟨rfl,rfl⟩
  · have hxp : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p) := by
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hx
      · simpa only [id_eq,segment_symm] using hx
    have hxq : x ∈ segment ℝ (drawingPieceStart P q) (drawingPieceEnd P q) := by
      rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hy
      · simpa only [id_eq,segment_symm] using hy
    obtain ⟨hpe,hqe⟩ := drawing_pieces_meeting_endpoints D P hmark p q hpq x hxp hxq
    have heab : x=a ∨ x=b := by
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hpe
      · exact hpe.symm
    have hecd : x=c ∨ x=d := by
      rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hqe
      · exact hqe.symm
    exact Or.inr (Or.inr (common_endpoint_alternatives a b c d x heab hecd))

theorem drawingSubdivisionGraph_finite_support [Fintype Edge] (P : ∀ e, PolygonalParametrization (D.edge e)) :
    {a : Plane | ∃ b, (drawingSubdivisionGraph P).Adj a b}.Finite := by
  have hf : (Set.range (drawingPieceStart P) ∪ Set.range (drawingPieceEnd P)).Finite :=
    (Set.finite_range _).union (Set.finite_range _)
  apply hf.subset
  rintro a ⟨b,hab,p,hp⟩
  rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Or.inl ⟨p,ha.symm⟩
  · exact Or.inr ⟨p,ha.symm⟩

end Paper170Geometry

end
end

section

/-! Prescribed subdivision points cannot lie in the interior of a graph segment. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D : Paper170.AdmissibleDrawing graph}

theorem subdivision_point_endpoint (P : ∀ e, PolygonalParametrization (D.edge e))
    (x : Plane) (hpoint : ∀ e t, D.edge e t=x → t ∈ Set.range (P e).knot)
    (e : Edge) (i : Fin (P e).pieces) (hx : x ∈ (P e).pieceTrace i) :
    x=D.edge e ((P e).knot i.castSucc) ∨ x=D.edge e ((P e).knot i.succ) := by
  obtain ⟨t,ht⟩ := (P e).pieceTrace_subset_range i hx
  obtain ⟨j,hj⟩ := hpoint e t ht
  have he : D.edge e ((P e).knot j)=x := (congrArg (D.edge e) hj).trans ht
  have hh := (P e).pieceTrace_knot_endpoint (D.edge_injective e) i j (he.symm ▸ hx)
  simpa only [he] using hh

theorem drawingSubdivisionGraph_point_endpoint (P : ∀ e, PolygonalParametrization (D.edge e))
    (x : Plane) (hpoint : ∀ e t, D.edge e t=x → t ∈ Set.range (P e).knot)
    (a b : Plane) (hab : (drawingSubdivisionGraph P).Adj a b) (hx : x ∈ segment ℝ a b) :
    x=a ∨ x=b := by
  obtain ⟨hab,p,hp⟩ := hab
  rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact subdivision_point_endpoint P x hpoint p.1 p.2 hx
  · have hx' : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p) := by
      simpa only [segment_symm] using hx
    exact (subdivision_point_endpoint P x hpoint p.1 p.2 hx').symm

end Paper170Geometry

end
end

section

/-! Each actual subdivided drawing edge is a simple walk of the constructed embedded graph. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D : Paper170.AdmissibleDrawing graph}

theorem drawingEdgeSequence_adj (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : Edge) (i : ℕ) (hi : i < (P e).pieces) :
    (drawingSubdivisionGraph P).Adj ((P e).vertices i) ((P e).vertices (i+1)) := by
  let j : Fin (P e).pieces := ⟨i,hi⟩
  have h0 : (P e).vertices i=drawingPieceStart P ⟨e,j⟩ := (P e).vertices_at j.castSucc
  have h1 : (P e).vertices (i+1)=drawingPieceEnd P ⟨e,j⟩ := (P e).vertices_at j.succ
  rw [h0,h1]
  exact drawingSubdivisionGraph_piece_adj P ⟨e,j⟩

def drawingEdgeWalk (P : ∀ e, PolygonalParametrization (D.edge e)) (e : Edge) :
    (drawingSubdivisionGraph P).Walk (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))) :=
  (graphSequenceWalk (drawingSubdivisionGraph P) (P e).vertices (P e).pieces
    (drawingEdgeSequence_adj P e)).copy (P e).vertices_first (P e).vertices_last

theorem drawingEdgeWalk_length (P : ∀ e, PolygonalParametrization (D.edge e)) (e : Edge) :
    (drawingEdgeWalk P e).length=(P e).pieces := by
  simp only [drawingEdgeWalk,SimpleGraph.Walk.length_copy,graphSequenceWalk_length]

theorem drawingEdgeWalk_getVert (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : Edge) (i : ℕ) (hi : i ≤ (P e).pieces) :
    (drawingEdgeWalk P e).getVert i=(P e).vertices i := by
  simp only [drawingEdgeWalk,SimpleGraph.Walk.getVert_copy]
  exact graphSequenceWalk_getVert _ _ _ _ i hi

theorem drawingEdgeWalk_isPath (P : ∀ e, PolygonalParametrization (D.edge e)) (e : Edge) :
    (drawingEdgeWalk P e).IsPath := by
  rw [drawingEdgeWalk,SimpleGraph.Walk.isPath_copy]
  apply graphSequenceWalk_isPath
  intro i hi j hj he
  change i ≤ (P e).pieces at hi
  change j ≤ (P e).pieces at hj
  have h0 := (P e).vertices_at (⟨i,by omega⟩ : Fin ((P e).pieces+1))
  have h1 := (P e).vertices_at (⟨j,by omega⟩ : Fin ((P e).pieces+1))
  rw [h0,h1] at he
  have hh := (P e).increasing.injective (D.edge_injective e he)
  exact congrArg Fin.val hh

theorem drawingEdgeWalk_uniqueVisit (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : Edge) (x : Plane) : UniqueWalkVisit (drawingEdgeWalk P e) x := by
  intro i j hi hj hix hjx
  exact (drawingEdgeWalk_isPath P e).getVert_injOn hi hj (hix.trans hjx.symm)

end Paper170Geometry

end
end

section

/-! Exact equality of the actual edge trace and its subdivision-graph walk realization. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D : Paper170.AdmissibleDrawing graph}

theorem drawingEdgeWalk_range_eq (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : Edge) :
    Set.range (graphWalkPath id (drawingEdgeWalk P e))=Set.range (D.edge e) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hlen := drawingEdgeWalk_length P e
    obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece (fun i => (drawingEdgeWalk P e).getVert i)
      (drawingEdgeWalk P e).length (by rw [hlen]; exact (P e).pieces_pos) x hx
    rw [hlen] at hi
    rw [drawingEdgeWalk_getVert P e i (by omega),drawingEdgeWalk_getVert P e (i+1) (by omega)] at hxi
    let j : Fin (P e).pieces := ⟨i,hi⟩
    have h0 : (P e).vertices i=D.edge e ((P e).knot j.castSucc) := (P e).vertices_at j.castSucc
    have h1 : (P e).vertices (i+1)=D.edge e ((P e).knot j.succ) := (P e).vertices_at j.succ
    rw [h0,h1] at hxi
    exact (P e).pieceTrace_subset_range j hxi
  · intro x hx
    obtain ⟨i,hi⟩ := ((P e).range_pieceTrace_iff x).mp hx
    apply polygonalArcPath_piece_subset_range (fun j => (drawingEdgeWalk P e).getVert j)
      (drawingEdgeWalk P e).length i.val (by rw [drawingEdgeWalk_length]; exact i.isLt)
    rw [drawingEdgeWalk_getVert P e i.val (by omega),drawingEdgeWalk_getVert P e (i.val+1) (by omega)]
    have h0 : (P e).vertices i.val=D.edge e ((P e).knot i.castSucc) := (P e).vertices_at i.castSucc
    have h1 : (P e).vertices (i.val+1)=D.edge e ((P e).knot i.succ) := (P e).vertices_at i.succ
    rw [h0,h1]
    exact hi

end Paper170Geometry

end
end

section

/-! Exact parameter-side control of actual graph-walk prefixes and suffixes. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem graphWalkPath_range_cases {V : Type*} {G : SimpleGraph V} (pos : V → Plane)
    {a b : V} (p : G.Walk a b) (x : Plane) (hx : x ∈ Set.range (graphWalkPath pos p)) :
    x=pos a ∨ ∃ i, i < p.length ∧ x ∈ segment ℝ (pos (p.getVert i)) (pos (p.getVert (i+1))) := by
  by_cases hp : p.length=0
  · change x ∈ Set.range (polygonalArcPath (fun i => pos (p.getVert i)) p.length) at hx
    rw [hp] at hx
    obtain ⟨t,ht⟩ := hx
    exact Or.inl (by simpa [polygonalArcPath,p.getVert_zero] using ht.symm)
  · exact Or.inr (polygonalArcPath_range_piece _ _ (by omega) x hx)

variable  {D : Paper170.AdmissibleDrawing graph}

theorem drawingEdgeWalk_take_trace (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : Edge) (k : Fin ((P e).pieces+1)) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P e).take k.val)) ⊆
      D.edge e '' Set.Icc (0 : unitInterval) ((P e).knot k) := by
  intro x hx
  rcases graphWalkPath_range_cases id ((drawingEdgeWalk P e).take k.val) x hx with he | ⟨i,hi,hxi⟩
  · exact ⟨0,⟨le_rfl,((P e).knot k).property.1⟩,(D.edge e).source.trans he.symm⟩
  · have hil : i < (P e).pieces := by
      rw [SimpleGraph.Walk.take_length,drawingEdgeWalk_length] at hi
      omega
    have hik : i+1 ≤ k.val := by
      rw [SimpleGraph.Walk.take_length,drawingEdgeWalk_length] at hi
      omega
    simp only [id_eq,SimpleGraph.Walk.take_getVert] at hxi
    rw [show min k.val i=i by omega,show min k.val (i+1)=i+1 by omega,
      drawingEdgeWalk_getVert P e i (by omega),drawingEdgeWalk_getVert P e (i+1) (by omega)] at hxi
    let j : Fin (P e).pieces := ⟨i,hil⟩
    have h0 : (P e).vertices i=D.edge e ((P e).knot j.castSucc) := (P e).vertices_at j.castSucc
    have h1 : (P e).vertices (i+1)=D.edge e ((P e).knot j.succ) := (P e).vertices_at j.succ
    rw [h0,h1] at hxi
    obtain ⟨t,ht⟩ := (P e).pieceTrace_parameter j x hxi
    have hbetween := intervalSegment_between ((P e).knot j.castSucc) ((P e).knot j.succ) t
      ((P e).increasing.monotone (by change i ≤ i+1; omega))
    exact ⟨intervalSegment ((P e).knot j.castSucc) ((P e).knot j.succ) t,
      ⟨(intervalSegment _ _ t).property.1,hbetween.2.trans ((P e).increasing.monotone hik)⟩,ht⟩

theorem drawingEdgeWalk_drop_trace (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : Edge) (k : Fin ((P e).pieces+1)) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P e).drop k.val)) ⊆
      D.edge e '' Set.Icc ((P e).knot k) (1 : unitInterval) := by
  intro x hx
  rcases graphWalkPath_range_cases id ((drawingEdgeWalk P e).drop k.val) x hx with he | ⟨i,hi,hxi⟩
  · refine ⟨(P e).knot k,⟨le_rfl,((P e).knot k).property.2⟩,?_⟩
    have hh : (drawingEdgeWalk P e).getVert k.val=D.edge e ((P e).knot k) :=
      (drawingEdgeWalk_getVert P e k.val (by omega)).trans ((P e).vertices_at k)
    exact hh.symm.trans he.symm
  · have hil : k.val+i < (P e).pieces := by
      rw [SimpleGraph.Walk.drop_length,drawingEdgeWalk_length] at hi
      omega
    simp only [id_eq,SimpleGraph.Walk.drop_getVert] at hxi
    rw [drawingEdgeWalk_getVert P e (k.val+i) (by omega),
      drawingEdgeWalk_getVert P e (k.val+(i+1)) (by omega)] at hxi
    let j : Fin (P e).pieces := ⟨k.val+i,hil⟩
    have h0 : (P e).vertices (k.val+i)=D.edge e ((P e).knot j.castSucc) := (P e).vertices_at j.castSucc
    have h1 : (P e).vertices (k.val+(i+1))=D.edge e ((P e).knot j.succ) := by
      have hh : (P e).vertices (k.val+i+1)=D.edge e ((P e).knot j.succ) := (P e).vertices_at j.succ
      simpa only [Nat.add_assoc] using hh
    rw [h0,h1] at hxi
    obtain ⟨t,ht⟩ := (P e).pieceTrace_parameter j x hxi
    have hbetween := intervalSegment_between ((P e).knot j.castSucc) ((P e).knot j.succ) t
      ((P e).increasing.monotone (by change k.val+i ≤ k.val+i+1; omega))
    refine ⟨intervalSegment ((P e).knot j.castSucc) ((P e).knot j.succ) t,⟨?_,?_⟩,ht⟩
    · exact ((P e).increasing.monotone (show k ≤ j.castSucc by change k.val ≤ k.val+i; omega)).trans hbetween.1
    · exact (intervalSegment _ _ t).property.2

end Paper170Geometry

end
end

end OAI
