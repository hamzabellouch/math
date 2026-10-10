import OAI.Combinatorics.CompleteCrossing.CrossingCuts
import OAI.Combinatorics.Crossing.PolygonalParametrizationCover

namespace OAI

/-! Reconnected paths and point-removing surgery on adjacent edges. -/

section

/-! The two actual switched walks, before loop deletion. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

theorem surgery_forward_adj : (crossingSurgeryGraph C P p q).Adj
    (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q)) :=
  crossingSurgeryGraph_reconnection_adj C P p q true

theorem surgery_backward_adj : (crossingSurgeryGraph C P p q).Adj
    (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p)) :=
  crossingSurgeryGraph_reconnection_adj C P p q false

def reconnectedForwardWalk (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex ((graph.src p.1))) (D'.vertex ((graph.dst q.1))) :=
  walkThroughChord (Kp.prefixInSurgery p q rfl)
    surgery_forward_adj (Kq.suffixInSurgery p q hm.symm)

def reconnectedBackwardWalk (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex ((graph.src q.1))) (D'.vertex ((graph.dst p.1))) :=
  walkThroughChord (Kq.prefixInSurgery p q hm.symm)
    surgery_backward_adj (Kp.suffixInSurgery p q rfl)

theorem reconnectedForwardWalk_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (graphWalkPath id (reconnectedForwardWalk Kp Kq hm))=
      (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take Kp.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).drop Kq.last.val)) := by
  rw [reconnectedForwardWalk,walkThroughChord_range,
    ExteriorCrossingCut.prefixInSurgery_trace,ExteriorCrossingCut.suffixInSurgery_trace]

theorem reconnectedBackwardWalk_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (graphWalkPath id (reconnectedBackwardWalk Kp Kq hm))=
      (Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).take Kq.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop Kp.last.val)) := by
  rw [reconnectedBackwardWalk,walkThroughChord_range,
    ExteriorCrossingCut.prefixInSurgery_trace,ExteriorCrossingCut.suffixInSurgery_trace]

end Paper170Geometry

end
end

section

/-! Actual simple polygonal paths extracted from the two switched walks. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

def reconnectedForwardPath (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) : Path (D'.vertex ((graph.src p.1))) (D'.vertex ((graph.dst q.1))) := by
  classical
  exact graphWalkPath id (reconnectedForwardWalk Kp Kq hm).bypass

def reconnectedBackwardPath (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) : Path (D'.vertex ((graph.src q.1))) (D'.vertex ((graph.dst p.1))) := by
  classical
  exact graphWalkPath id (reconnectedBackwardWalk Kp Kq hm).bypass

theorem reconnectedForwardPath_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (reconnectedForwardPath Kp Kq hm) := by
  classical
  exact graphWalkPath_injective id hemb (surgery_mixed_endpoints_ne C p q hadj)
    _ (reconnectedForwardWalk Kp Kq hm).bypass_isPath

theorem reconnectedBackwardPath_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (reconnectedBackwardPath Kp Kq hm) := by
  classical
  exact graphWalkPath_injective id hemb (surgery_mixed_endpoints_ne C q p (hadj.imp Eq.symm Eq.symm))
    _ (reconnectedBackwardWalk Kp Kq hm).bypass_isPath

theorem reconnectedForwardPath_hasFiniteAffineCover (Kp : ExteriorCrossingCut C P p)
    (Kq : ExteriorCrossingCut C P q) (hm : C.innerMark p=C.innerMark q) :
    HasFiniteAffineCover (reconnectedForwardPath Kp Kq hm) := by
  classical
  exact graphWalkPath_hasFiniteAffineCover id _

theorem reconnectedBackwardPath_hasFiniteAffineCover (Kp : ExteriorCrossingCut C P p)
    (Kq : ExteriorCrossingCut C P q) (hm : C.innerMark p=C.innerMark q) :
    HasFiniteAffineCover (reconnectedBackwardPath Kp Kq hm) := by
  classical
  exact graphWalkPath_hasFiniteAffineCover id _

theorem reconnectedForwardPath_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (reconnectedForwardPath Kp Kq hm) ⊆
      (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take Kp.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).drop Kq.last.val)) := by
  classical
  exact (graphWalkPath_bypass_range_subset id (reconnectedForwardWalk Kp Kq hm)).trans
    (by rw [reconnectedForwardWalk_trace])

theorem reconnectedBackwardPath_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (reconnectedBackwardPath Kp Kq hm) ⊆
      (Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).take Kq.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop Kp.last.val)) := by
  classical
  exact (graphWalkPath_bypass_range_subset id (reconnectedBackwardWalk Kp Kq hm)).trans
    (by rw [reconnectedBackwardWalk_trace])

end Paper170Geometry

end
end

section

/-! The selected spatial crossing point is absent from both actual bypassed paths. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

theorem reconnected_paths_avoid_crossing (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (x : Plane)
    (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∉ Set.range (reconnectedForwardPath Kp Kq hm) ∧
      x ∉ Set.range (reconnectedBackwardPath Kp Kq hm) := by
  obtain ⟨hxin,havoid⟩ := C.reconnection_avoids_chord_meeting p q hpq x hxp hxq
  have hxinq : x ∈ C.crossingDisk q := by
    simpa only [DrawingPassages.crossingDisk,hm] using hxin
  constructor
  · intro hx
    rcases reconnectedForwardPath_trace Kp Kq hm hx with (hx | hx) | hx
    · exact Set.disjoint_left.mp Kp.prefix_outside hx hxin
    · exact havoid true hx
    · exact Set.disjoint_left.mp Kq.suffix_outside hx hxinq
  · intro hx
    rcases reconnectedBackwardPath_trace Kp Kq hm hx with (hx | hx) | hx
    · exact Set.disjoint_left.mp Kq.prefix_outside hx hxinq
    · exact havoid false hx
    · exact Set.disjoint_left.mp Kp.suffix_outside hx hxin

end Paper170Geometry

end
end

section

/-! The actual rerouted simple paths have vertex-avoiding interiors. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

theorem path_interior_avoids_vertices_of_range {V : Type*} (vertex : V → Plane) (a b : V)
    (γ : Path (vertex a) (vertex b)) (hinj : Function.Injective γ)
    (hrange : ∀ v, vertex v ∈ Set.range γ → v=a ∨ v=b)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (v : V) : γ t ≠ vertex v := by
  intro he
  rcases hrange v ⟨t,he⟩ with rfl | rfl
  · exact ht.1.ne (hinj (he.trans γ.source.symm)).symm
  · exact ht.2.ne (hinj (he.trans γ.target.symm))

theorem reconnectedForwardPath_vertex_eq (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (j : Vertex) (hj : D'.vertex j ∈ Set.range (reconnectedForwardPath Kp Kq hm)) :
    j=(graph.src p.1) ∨ j=(graph.dst q.1) := by
  rcases reconnectedForwardPath_trace Kp Kq hm hj with (hj | hj) | hj
  · exact Or.inl (Kp.prefix_vertex_eq j hj)
  · exact False.elim (C.reconnection_segment_avoids_vertices p q hm D'.vertex hv true j hj)
  · exact Or.inr (Kq.suffix_vertex_eq j hj)

theorem reconnectedBackwardPath_vertex_eq (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (j : Vertex) (hj : D'.vertex j ∈ Set.range (reconnectedBackwardPath Kp Kq hm)) :
    j=(graph.src q.1) ∨ j=(graph.dst p.1) := by
  rcases reconnectedBackwardPath_trace Kp Kq hm hj with (hj | hj) | hj
  · exact Or.inl (Kq.prefix_vertex_eq j hj)
  · exact False.elim (C.reconnection_segment_avoids_vertices p q hm D'.vertex hv false j hj)
  · exact Or.inr (Kp.suffix_vertex_eq j hj)

theorem reconnectedForwardPath_interior_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : Vertex) :
    reconnectedForwardPath Kp Kq hm t ≠ D'.vertex j :=
  path_interior_avoids_vertices_of_range D'.vertex _ _ _
    (reconnectedForwardPath_injective Kp Kq hm hadj hemb)
    (reconnectedForwardPath_vertex_eq Kp Kq hm hv) t ht j

theorem reconnectedBackwardPath_interior_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : Vertex) :
    reconnectedBackwardPath Kp Kq hm t ≠ D'.vertex j :=
  path_interior_avoids_vertices_of_range D'.vertex _ _ _
    (reconnectedBackwardPath_injective Kp Kq hm hadj hemb)
    (reconnectedBackwardPath_vertex_eq Kp Kq hm hv) t ht j

end Paper170Geometry

end
end

section

/-! Replacement of two actual drawing routes with proved simple, vertex-avoiding paths. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170.ContinuousDrawing
def replaceTwoRoutes (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f))))
    (g : Edge) : Path (D.vertex ((graph.src g))) (D.vertex ((graph.dst g))) := by
  classical
  exact if h : g=e then γ.cast (congrArg (fun k : Edge => D.vertex ((graph.src k))) h)
    (congrArg (fun k : Edge => D.vertex ((graph.dst k))) h)
  else if h : g=f then δ.cast (congrArg (fun k : Edge => D.vertex ((graph.src k))) h)
    (congrArg (fun k : Edge => D.vertex ((graph.dst k))) h)
  else D.edge g

theorem replaceTwoRoutes_first (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f)))) :
    D.replaceTwoRoutes e f γ δ e=γ := by
  simp only [replaceTwoRoutes,dite_eq_left rfl,Path.cast_rfl_rfl]

theorem replaceTwoRoutes_second (D : Paper170.ContinuousDrawing graph) (e f : Edge) (hef : e ≠ f)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f)))) :
    D.replaceTwoRoutes e f γ δ f=δ := by
  simp only [replaceTwoRoutes,dite_eq_right (Ne.symm hef),dite_eq_left rfl,Path.cast_rfl_rfl]

theorem replaceTwoRoutes_other (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f))))
    (g : Edge) (hge : g ≠ e) (hgf : g ≠ f) :
    D.replaceTwoRoutes e f γ δ g=D.edge g := by
  simp only [replaceTwoRoutes,dite_eq_right hge,dite_eq_right hgf]

def replaceTwoEdges (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f))))
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hvγ : ∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → ∀ j, γ t ≠ D.vertex j)
    (hvδ : ∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → ∀ j, δ t ≠ D.vertex j) :
    Paper170.ContinuousDrawing graph where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  edge := D.replaceTwoRoutes e f γ δ
  edge_injective := by
    intro g
    classical
    by_cases hge : g=e
    · subst g
      rw [replaceTwoRoutes_first]
      exact hγ
    by_cases hgf : g=f
    · subst g
      rw [replaceTwoRoutes_second _ _ _ (Ne.symm hge)]
      exact hδ
    · rw [replaceTwoRoutes_other _ _ _ _ _ _ hge hgf]
      exact D.edge_injective g
  interior_avoids_vertices := by
    intro g t ht j
    classical
    by_cases hge : g=e
    · subst g
      rw [replaceTwoRoutes_first]
      exact hvγ t ht j
    by_cases hgf : g=f
    · subst g
      rw [replaceTwoRoutes_second _ _ _ (Ne.symm hge)]
      exact hvδ t ht j
    · rw [replaceTwoRoutes_other _ _ _ _ _ _ hge hgf]
      exact D.interior_avoids_vertices g t ht j

end Paper170.ContinuousDrawing

end
end

section

/-! Trace case analysis for the actual two-route replacement. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170.ContinuousDrawing
theorem replaceTwoRoutes_range_cases (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f))))
    (g : Edge) (x : Plane) (hx : x ∈ Set.range (D.replaceTwoRoutes e f γ δ g)) :
    (g=e ∧ x ∈ Set.range γ) ∨ (g=f ∧ x ∈ Set.range δ) ∨
      (g ≠ e ∧ g ≠ f ∧ x ∈ Set.range (D.edge g)) := by
  classical
  by_cases hge : g=e
  · subst g
    exact Or.inl ⟨rfl,by simpa only [replaceTwoRoutes_first] using hx⟩
  by_cases hgf : g=f
  · subst g
    exact Or.inr (Or.inl ⟨rfl,by simpa only [replaceTwoRoutes_second D e f (Ne.symm hge)] using hx⟩)
  · exact Or.inr (Or.inr ⟨hge,hgf,by simpa only [replaceTwoRoutes_other D e f γ δ g hge hgf] using hx⟩)

end Paper170.ContinuousDrawing

end
end

section

/-! Assigning the two switched paths to the original edges for either shared endpoint. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

def adjacentSurgeryRouteP (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1)) :
    Path (D'.vertex ((graph.src p.1))) (D'.vertex ((graph.dst p.1))) := by
  classical
  exact if h : (graph.src p.1)=(graph.src q.1) then (reconnectedBackwardPath Kp Kq hm).cast
    (congrArg (fun i => D'.vertex (i)) h) rfl
  else (reconnectedForwardPath Kp Kq hm).cast rfl
    (congrArg (fun j => D'.vertex (j)) (hadj.resolve_left h))

def adjacentSurgeryRouteQ (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1)) :
    Path (D'.vertex ((graph.src q.1))) (D'.vertex ((graph.dst q.1))) := by
  classical
  exact if h : (graph.src p.1)=(graph.src q.1) then (reconnectedForwardPath Kp Kq hm).cast
    (congrArg (fun i => D'.vertex (i)) h.symm) rfl
  else (reconnectedBackwardPath Kp Kq hm).cast rfl
    (congrArg (fun j => D'.vertex (j)) (hadj.resolve_left h).symm)

theorem adjacentSurgeryRouteP_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (adjacentSurgeryRouteP Kp Kq hm hadj) := by
  unfold adjacentSurgeryRouteP
  split
  · exact reconnectedBackwardPath_injective Kp Kq hm hadj hemb
  · exact reconnectedForwardPath_injective Kp Kq hm hadj hemb

theorem adjacentSurgeryRouteQ_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (adjacentSurgeryRouteQ Kp Kq hm hadj) := by
  unfold adjacentSurgeryRouteQ
  split
  · exact reconnectedForwardPath_injective Kp Kq hm hadj hemb
  · exact reconnectedBackwardPath_injective Kp Kq hm hadj hemb

theorem adjacentSurgeryRouteP_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : Vertex) :
    adjacentSurgeryRouteP Kp Kq hm hadj t ≠ D'.vertex j := by
  unfold adjacentSurgeryRouteP
  split
  · exact reconnectedBackwardPath_interior_avoids_vertices Kp Kq hm hv hadj hemb t ht j
  · exact reconnectedForwardPath_interior_avoids_vertices Kp Kq hm hv hadj hemb t ht j

theorem adjacentSurgeryRouteQ_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : Vertex) :
    adjacentSurgeryRouteQ Kp Kq hm hadj t ≠ D'.vertex j := by
  unfold adjacentSurgeryRouteQ
  split
  · exact reconnectedForwardPath_interior_avoids_vertices Kp Kq hm hv hadj hemb t ht j
  · exact reconnectedBackwardPath_interior_avoids_vertices Kp Kq hm hv hadj hemb t ht j

end Paper170Geometry

end
end

section

/-! An actual continuous drawing with the two adjacent routes replaced. Admissibility is a later theorem. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

def adjacentSurgeryDrawing (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) : Paper170.ContinuousDrawing graph :=
  D'.toContinuousDrawing.replaceTwoEdges p.1 q.1
    (adjacentSurgeryRouteP Kp Kq hm hadj) (adjacentSurgeryRouteQ Kp Kq hm hadj)
    (adjacentSurgeryRouteP_injective Kp Kq hm hadj hemb)
    (adjacentSurgeryRouteQ_injective Kp Kq hm hadj hemb)
    (adjacentSurgeryRouteP_avoids_vertices Kp Kq hm hadj hv hemb)
    (adjacentSurgeryRouteQ_avoids_vertices Kp Kq hm hadj hv hemb)

theorem adjacentSurgeryDrawing_vertex (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).vertex=D'.vertex := rfl

theorem adjacentSurgeryDrawing_first (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge p.1=adjacentSurgeryRouteP Kp Kq hm hadj :=
  Paper170.ContinuousDrawing.replaceTwoRoutes_first _ _ _ _ _

theorem adjacentSurgeryDrawing_second (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge q.1=adjacentSurgeryRouteQ Kp Kq hm hadj :=
  Paper170.ContinuousDrawing.replaceTwoRoutes_second _ _ _ (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)) _ _

theorem adjacentSurgeryDrawing_other (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge e=D'.edge e :=
  Paper170.ContinuousDrawing.replaceTwoRoutes_other _ _ _ _ _ _ hep heq

theorem adjacentSurgeryRouteP_hasFiniteAffineCover
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1)) :
    HasFiniteAffineCover (adjacentSurgeryRouteP Kp Kq hm hadj) := by
  unfold adjacentSurgeryRouteP
  split
  · exact (reconnectedBackwardPath_hasFiniteAffineCover Kp Kq hm).cast _ _
  · exact (reconnectedForwardPath_hasFiniteAffineCover Kp Kq hm).cast _ _

theorem adjacentSurgeryRouteQ_hasFiniteAffineCover
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1)) :
    HasFiniteAffineCover (adjacentSurgeryRouteQ Kp Kq hm hadj) := by
  unfold adjacentSurgeryRouteQ
  split
  · exact (reconnectedForwardPath_hasFiniteAffineCover Kp Kq hm).cast _ _
  · exact (reconnectedBackwardPath_hasFiniteAffineCover Kp Kq hm).cast _ _

end Paper170Geometry

end
end

section

/-! Polygonality and actual removal of the selected point from every new drawing route. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

theorem adjacentSurgeryDrawing_hasFiniteAffineCover
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (e : Edge) : HasFiniteAffineCover ((adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge e) := by
  classical
  by_cases hep : e=p.1
  · subst e
    rw [adjacentSurgeryDrawing_first]
    exact adjacentSurgeryRouteP_hasFiniteAffineCover Kp Kq hm hadj
  by_cases heq : e=q.1
  · subst e
    rw [adjacentSurgeryDrawing_second Kp Kq hm hpq]
    exact adjacentSurgeryRouteQ_hasFiniteAffineCover Kp Kq hm hadj
  · rw [adjacentSurgeryDrawing_other Kp Kq hm hadj hv hemb e hep heq]
    exact (P e).hasFiniteAffineCover

theorem adjacentSurgeryRoutes_avoid_crossing
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∉ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∧
      x ∉ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj) := by
  have ha := reconnected_paths_avoid_crossing Kp Kq hm hpq x hxp hxq
  constructor
  · unfold adjacentSurgeryRouteP
    split
    · exact ha.2
    · exact ha.1
  · unfold adjacentSurgeryRouteQ
    split
    · exact ha.1
    · exact ha.2

theorem adjacentSurgeryDrawing_avoids_crossing
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q))
    (hother : ∀ e, e ≠ p.1 → e ≠ q.1 → x ∉ Set.range (D'.edge e)) :
    ∀ e, x ∉ Set.range ((adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge e) := by
  have ha := adjacentSurgeryRoutes_avoid_crossing Kp Kq hm hpq hadj x hxp hxq
  intro e
  classical
  by_cases hep : e=p.1
  · subst e
    rw [adjacentSurgeryDrawing_first]
    exact ha.1
  by_cases heq : e=q.1
  · subst e
    rw [adjacentSurgeryDrawing_second Kp Kq hm hpq]
    exact ha.2
  · rw [adjacentSurgeryDrawing_other Kp Kq hm hadj hv hemb e hep heq]
    exact hother e hep heq

end Paper170Geometry

end
end

section

/-! All cut and embedding data are constructed for the actual normalized drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem exists_adjacentSurgery_continuousDrawing [Fintype Vertex] [Fintype Edge] (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    ∃ A : Paper170.ContinuousDrawing graph, A.vertex=v ∧
      (∀ e, HasFiniteAffineCover (A.edge e)) ∧
      (∀ e, x ∉ Set.range (A.edge e)) ∧
      (∀ e, e ≠ p.1 → e ≠ q.1 → ∀ t, A.edge e t=E.assembledEdge v e t) := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  have hcross := C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq
  obtain ⟨P,hmark,hport⟩ := E.exists_assembled_port_subdivision v hvinj hv hdet
  obtain ⟨Kp⟩ := E.nonempty_exteriorCrossingCut v hvinj hv hdet P hport p
  obtain ⟨Kq⟩ := E.nonempty_exteriorCrossingCut v hvinj hv hdet P hport q
  have hemb := crossingSurgeryGraph_embedding C P hmark hport p q hm hcross
  let A := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  refine ⟨A,rfl,adjacentSurgeryDrawing_hasFiniteAffineCover Kp Kq hm hpq hadj hv hemb,?_,?_⟩
  · apply adjacentSurgeryDrawing_avoids_crossing Kp Kq hm hpq hadj hv hemb x hxp hxq
    intro e hep heq hx
    exact Set.disjoint_left.mp (E.assembled_other_edge_avoids_crossingDisk v hv p q hpq hm e hep heq)
      hx (C.reconnection_avoids_chord_meeting p q hpq x hxp hxq).1
  · intro e hep heq t
    exact congrArg (fun γ => γ t) (adjacentSurgeryDrawing_other Kp Kq hm hadj hv hemb e hep heq)

end Paper170Geometry.PolygonalExterior

end
end

end OAI
