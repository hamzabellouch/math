import OAI.Combinatorics.CompleteCrossing.LocalGeometry
import OAI.Combinatorics.Crossing.ChainPieceInteriors
import OAI.Combinatorics.Crossing.ChainTracePieces
import OAI.Combinatorics.Crossing.DrawingSpokePorts
import OAI.Combinatorics.Crossing.IncidentSpokePorts
import OAI.Combinatorics.Crossing.MinimumChainVertexPieces
import OAI.Combinatorics.Crossing.ShortVertexRadius
import OAI.Combinatorics.Crossing.VertexPieceClearance
import OAI.Combinatorics.Crossing.VertexSpokeBounds
import OAI.Combinatorics.Crossing.VertexTraceDisks

namespace OAI

/-! Chain pieces near vertices, incident spoke ports, and short vertex radii. -/

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem drawing_chain_piece_vertex (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) (j : Vertex)
    (hx : D.vertex j ∈ segment ℝ (P.vertices i) (P.vertices (i+1))) :
    (j=(graph.src e) ∧ i=0) ∨ (j=(graph.dst e) ∧ i+1=P.pieces) := by
  obtain ⟨t,ht⟩ := P.inside i hi hx
  rcases drawing_edge_vertex_parameter D e t j ht with ⟨_,he⟩ | ⟨_,he⟩
  · have hx0 : P.vertices 0 ∈ segment ℝ (P.vertices i) (P.vertices (i+1)) := by
      simpa only [P.first,he] using hx
    have hh := P.minimum_vertex_piece_index hmin i 0 hi (by omega) hx0
    exact Or.inl ⟨he,by omega⟩
  · have hxN : P.vertices P.pieces ∈ segment ℝ (P.vertices i) (P.vertices (i+1)) := by
      simpa only [P.last,he] using hx
    have hh := P.minimum_vertex_piece_index hmin i P.pieces hi (by omega) hxN
    exact Or.inr ⟨he,by omega⟩

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem drawing_chain_range_eq (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e)))) :
    Set.range P.path=Set.range (D.edge e) :=
  path_range_eq_of_subset (D.edge e) P.path (D.edge_injective e) P.path_range_subset

theorem drawing_chain_pieces_pos (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e)))) :
    0 < P.pieces := by
  apply P.pieces_pos_of_ne
  intro h
  exact graph.loopless e (D.vertex_injective h)

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem drawing_chain_piece_open_subset_interior (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) :
    openSegmentTrace (P.vertices i) (P.vertices (i+1)) ⊆ Paper170.edgeInterior D e := by
  intro x hx
  have hseg := openSegmentTrace_subset_segment _ _ hx
  have hne := openSegmentTrace_ne_endpoints _ _
    (P.minimum_vertices_ne hmin i (i+1) (by omega) (by omega)) x hx
  apply edgeInterior_of_range_not_vertices D e x (P.inside i hi hseg)
  intro j hj
  have hvertex : D.vertex j ∈ segment ℝ (P.vertices i) (P.vertices (i+1)) := hj ▸ hseg
  rcases drawing_chain_piece_vertex D e P hmin i hi j hvertex with ⟨he,hii⟩ | ⟨he,hii⟩
  · apply hne.1
    calc
      x = D.vertex j := hj
      _ = D.vertex ((graph.src e)) := congrArg D.vertex he
      _ = P.vertices i := by simpa only [hii] using P.first.symm
  · apply hne.2
    calc
      x = D.vertex j := hj
      _ = D.vertex ((graph.dst e)) := congrArg D.vertex he
      _ = P.vertices (i+1) := by simpa only [hii] using P.last.symm

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem exists_vertex_piece_clearance [Fintype Vertex] [Fintype Edge] (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces) :
    ∃ r : ℝ, 0 < r ∧
      (∀ j k, j ≠ k → Disjoint (closedRoundDisk (D.vertex j) r) (closedRoundDisk (D.vertex k) r)) ∧
      (∀ j e (i : Fin (P e).pieces),
        ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
        Disjoint (closedRoundDisk (D.vertex j) r)
          (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1)))) := by
  classical
  let Bad := Σ j : Vertex, Σ e : Edge,
    {i : Fin (P e).pieces // ¬ ((j=(graph.src e) ∧ i.val=0) ∨
      (j=(graph.dst e) ∧ i.val+1=(P e).pieces))}
  let K : Bad → Set Plane := fun t =>
    segment ℝ ((P t.2.1).vertices t.2.2.val.val) ((P t.2.1).vertices (t.2.2.val.val+1))
  have hK (t : Bad) : IsCompact (K t) := by
    dsimp [K]
    rw [← Path.range_segment]
    exact isCompact_range (Path.segment _ _).continuous
  have hnot (t : Bad) : D.vertex t.1 ∉ K t := by
    intro hx
    exact t.2.2.property (drawing_chain_piece_vertex D t.2.1 (P t.2.1)
      (hmin t.2.1) t.2.2.val.val t.2.2.val.isLt t.1 hx)
  obtain ⟨ρ,hρ,hclear⟩ := exists_round_disk_clearance (fun t : Bad => D.vertex t.1) K hK hnot
  obtain ⟨σ,hσ,hdis⟩ := exists_disjoint_round_disks D.vertex D.vertex_injective
  refine ⟨min ρ σ,lt_min hρ hσ,?_,?_⟩
  · intro j k hjk
    exact (hdis j k hjk).mono
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
  · intro j e i hi
    exact (hclear ⟨j,e,⟨i,hi⟩⟩).mono_left
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_left _ _))

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem drawing_chain_startPort_interior (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r) (hshort : r^2 < squaredLength (P.vertices 1-P.vertices 0)) :
    P.startPort r ∈ Paper170.edgeInterior D e := by
  exact drawing_chain_piece_open_subset_interior D e P hmin 0 (drawing_chain_pieces_pos D e P)
    (radialPort_mem_openSegment _ _ r hr hshort)

theorem drawing_chain_endPort_interior (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    P.endPort r ∈ Paper170.edgeInterior D e := by
  have hp := drawing_chain_pieces_pos D e P
  have hs : r^2 < squaredLength (P.vertices (P.pieces-1)-P.vertices P.pieces) := by
    rwa [squaredLength_sub_comm]
  have hx := openSegmentTrace_reverse_mem _ _ _ (radialPort_mem_openSegment _ _ r hr hs)
  apply drawing_chain_piece_open_subset_interior D e P hmin (P.pieces-1) (by omega)
  simpa only [PolygonalChain.endPort,show P.pieces-1+1=P.pieces by omega] using hx

theorem drawing_chain_startPort_circle (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces) (r : ℝ) :
    squaredLength (P.startPort r-D.vertex ((graph.src e)))=r^2 := by
  have hp := drawing_chain_pieces_pos D e P
  have h := radialPort_on_circle (P.vertices 0) (P.vertices 1)
    (P.minimum_vertices_ne hmin 0 1 (by omega) hp) r
  simpa only [PolygonalChain.startPort,P.first] using h

theorem drawing_chain_endPort_circle (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces) (r : ℝ) :
    squaredLength (P.endPort r-D.vertex ((graph.dst e)))=r^2 := by
  have hp := drawing_chain_pieces_pos D e P
  have h := radialPort_on_circle (P.vertices P.pieces) (P.vertices (P.pieces-1))
    (Ne.symm (P.minimum_vertices_ne hmin (P.pieces-1) P.pieces (by omega) (by omega))) r
  simpa only [PolygonalChain.endPort,P.last] using h

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem exists_vertex_trace_disks [Fintype Vertex] [Fintype Edge] (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces) :
    ∃ r : ℝ, 0 < r ∧
      (∀ j k, j ≠ k → Disjoint (closedRoundDisk (D.vertex j) r) (closedRoundDisk (D.vertex k) r)) ∧
      (∀ j e x, x ∈ closedRoundDisk (D.vertex j) r →
        (x ∈ Set.range (D.edge e) ↔
          (j=(graph.src e) ∧ x ∈ segment ℝ ((P e).vertices 0) ((P e).vertices 1)) ∨
          (j=(graph.dst e) ∧ x ∈ segment ℝ ((P e).vertices ((P e).pieces-1)) ((P e).vertices (P e).pieces)))) := by
  classical
  obtain ⟨r,hr,hdis,hclear⟩ := exists_vertex_piece_clearance D P hmin
  refine ⟨r,hr,hdis,?_⟩
  intro j e x hxd
  have hpos := drawing_chain_pieces_pos D e (P e)
  constructor
  · intro hx
    rw [← drawing_chain_range_eq D e (P e)] at hx
    obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece (P e).vertices (P e).pieces hpos x hx
    have hinc : (j=(graph.src e) ∧ i=0) ∨ (j=(graph.dst e) ∧ i+1=(P e).pieces) := by
      by_contra h
      exact Set.disjoint_left.mp (hclear j e ⟨i,hi⟩ h) hxd hxi
    rcases hinc with ⟨hj,hii⟩ | ⟨hj,hii⟩
    · exact Or.inl ⟨hj,by simpa only [hii] using hxi⟩
    · have hlast : i=(P e).pieces-1 := by omega
      exact Or.inr ⟨hj,by simpa only [hlast,show (P e).pieces-1+1=(P e).pieces by omega] using hxi⟩
  · rintro (⟨hj,hx⟩ | ⟨hj,hx⟩)
    · exact (P e).inside 0 hpos hx
    · have hi : (P e).pieces-1 < (P e).pieces := by omega
      apply (P e).inside ((P e).pieces-1) hi
      simpa only [show (P e).pieces-1+1=(P e).pieces by omega] using hx

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
def IncidentEdges (graph : Paper170.Graph Vertex Edge) (j : Vertex) :=
  {e : Edge // j=(graph.src e) ∨ j=(graph.dst e)}

instance incidentEdgesFintype [Fintype Edge] (j : Vertex) : Fintype (IncidentEdges graph j) := by
  classical
  unfold IncidentEdges
  infer_instance

theorem incident_edges_adjacent (j : Vertex) (e f : IncidentEdges graph j) :
    graph.src e.val=graph.src f.val ∨ graph.src e.val=graph.dst f.val ∨
      graph.dst e.val=graph.src f.val ∨ graph.dst e.val=graph.dst f.val := by
  rcases e.property with he | he <;> rcases f.property with hf | hf
  · exact Or.inl (he.symm.trans hf)
  · exact Or.inr (Or.inl (he.symm.trans hf))
  · exact Or.inr (Or.inr (Or.inl (he.symm.trans hf)))
  · exact Or.inr (Or.inr (Or.inr (he.symm.trans hf)))

def drawingSpokePort (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (r : ℝ) (j : Vertex) (e : IncidentEdges graph j) : Plane :=
  if j=graph.src e.val then (P e.val).startPort r else (P e.val).endPort r

theorem drawingSpokePort_interior (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (j : Vertex) (e : IncidentEdges graph j) :
    drawingSpokePort D P r j e ∈ Paper170.edgeInterior D e.val := by
  unfold drawingSpokePort
  split_ifs
  · exact drawing_chain_startPort_interior D e.val (P e.val) (hmin e.val) r hr (hshort e.val).1
  · exact drawing_chain_endPort_interior D e.val (P e.val) (hmin e.val) r hr (hshort e.val).2

theorem drawingSpokePort_circle (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (j : Vertex) (e : IncidentEdges graph j) :
    squaredLength (drawingSpokePort D P r j e-D.vertex j)=r^2 := by
  unfold drawingSpokePort
  split_ifs with h
  · simpa only [h] using drawing_chain_startPort_circle D e.val (P e.val) (hmin e.val) r
  · have he := e.property.resolve_left h
    simpa only [he] using drawing_chain_endPort_circle D e.val (P e.val) (hmin e.val) r

theorem drawingSpokePort_injective (D : Paper170.AdmissibleDrawing graph) (hnorm : NoAdjacentCrossings D)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (j : Vertex) : Function.Injective (drawingSpokePort D.toContinuousDrawing P r j) := by
  intro e f heq
  by_contra hne
  have hef : e.val ≠ f.val := fun h => hne (Subtype.ext h)
  have hp := drawingSpokePort_interior D.toContinuousDrawing P hmin r hr hshort j e
  have hq := drawingSpokePort_interior D.toContinuousDrawing P hmin r hr hshort j f
  rw [← heq] at hq
  have hh : drawingSpokePort D.toContinuousDrawing P r j e ∈
      Paper170.edgeInterior D.toContinuousDrawing e.val ∩ Paper170.edgeInterior D.toContinuousDrawing f.val := ⟨hp,hq⟩
  rw [hnorm.eq_empty e.val f.val hef (incident_edges_adjacent j e f)] at hh
  exact hh

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem exists_vertex_spoke_bound [Fintype Edge] (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ e,
      r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
  let L : Edge → ℝ := fun e =>
    min (squaredLength ((P e).vertices 1-(P e).vertices 0))
      (squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
  have hL (e : Edge) : 0 < L e := by
    have hp := drawing_chain_pieces_pos D e (P e)
    have hlast := (P e).minimum_piece_ne_zero (hmin e) ((P e).pieces-1) (by omega)
    rw [show (P e).pieces-1+1=(P e).pieces by omega] at hlast
    exact lt_min (squaredLength_pos _ ((P e).minimum_piece_ne_zero (hmin e) 0 hp))
      (squaredLength_pos _ hlast)
  obtain ⟨r,hr,hrρ,hbound⟩ := exists_small_squared_radius ρ hρ L hL
  exact ⟨r,hr,hrρ,fun e => ⟨(hbound e).trans_le (min_le_left _ _),
    (hbound e).trans_le (min_le_right _ _)⟩⟩

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem exists_short_vertex_radius [Fintype Edge] (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ e,
      4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
  obtain ⟨s,hs,hsρ,hbound⟩ := exists_vertex_spoke_bound D P hmin ρ hρ
  refine ⟨s/2,by positivity,by linarith,?_⟩
  intro e
  obtain ⟨hfirst,hlast⟩ := hbound e
  constructor <;> nlinarith

end Paper170Geometry

end
end

end OAI
