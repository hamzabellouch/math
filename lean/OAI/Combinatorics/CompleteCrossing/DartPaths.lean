import OAI.Combinatorics.CompleteCrossing.CycleSpace
import OAI.Combinatorics.CompleteCrossing.Tracks
import OAI.Combinatorics.Crossing.FinitePolygonalComposition
import OAI.Combinatorics.Crossing.PolygonalEndpointCasts

namespace OAI

/-! Drawn-edge chains, dart-path realizations, and endpoint-flag pairing. -/

section

/-! Incident flags of an oriented traversal in an arbitrary finite simple graph. -/
noncomputable section
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

instance [Fintype Edge] : Fintype (OrientedDart graph) :=
  Fintype.ofEquiv (Edge × Bool)
    { toFun := fun p => ⟨p.1,p.2⟩
      invFun := fun d => (d.edge,d.forward)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def dartSourceIncident (d : OrientedDart graph) : IncidentEdges graph d.fst :=
  ⟨d.edge,dart_source_incident d⟩

def dartTargetIncident (d : OrientedDart graph) : IncidentEdges graph d.snd :=
  ⟨d.edge,dart_target_incident d⟩

@[simp] theorem OrientedDart.symm_edge (d : OrientedDart graph) : d.symm.edge = d.edge := rfl

end Paper170Geometry

end
end

section

/-! Actual edge paths between vertex circles, and actual shifted paths with both exterior connectors. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

def trackChain (e : Edge) : PolygonalChain Set.univ (V.startPort e) (V.endPort e) where
  pieces := V.pieces e
  vertices := V.vertices e
  first := V.vertices_first e
  last := V.vertices_last e
  start_mem := Set.mem_univ _
  inside := fun _ _ => Set.subset_univ _

def chordChain (j : Vertex) (a b : IncidentEdges graph j) :
    PolygonalChain Set.univ (V.spokePort j a) (V.spokePort j b) :=
  PolygonalChain.single Set.univ _ _ (Set.mem_univ _) (Set.subset_univ _)

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

def shiftedTrackChain (e : Edge) (ε : ℝ) :
    PolygonalChain Set.univ (C.tangentPort ((graph.src e)) (V.leftIncident e) ε)
      (C.tangentPort ((graph.dst e)) (V.rightIncident e) ε) where
  pieces := V.pieces e
  vertices := shiftedTrack (V.vertices e) (V.pieces e) ε
  first := V.shiftedTrack_first C e ε
  last := V.shiftedTrack_last C e ε
  start_mem := Set.mem_univ _
  inside := fun _ _ => Set.subset_univ _

def connectorChain (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort j e ε) (C.tangentPort j e ε) :=
  PolygonalChain.single Set.univ _ _ (Set.mem_univ _) (Set.subset_univ _)

def shiftedEdgeChain (e : Edge) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort ((graph.src e)) (V.leftIncident e) ε)
      (C.shiftedPort ((graph.dst e)) (V.rightIncident e) ε) :=
  ((C.connectorChain ((graph.src e)) (V.leftIncident e) ε).join (C.shiftedTrackChain e ε)).join
    (C.connectorChain ((graph.dst e)) (V.rightIncident e) ε).reverse

def shiftedChordChain (j : Vertex) (a b : IncidentEdges graph j) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort j a ε) (C.shiftedPort j b ε) :=
  PolygonalChain.single Set.univ _ _ (Set.mem_univ _) (Set.subset_univ _)

theorem shiftedEdgeChain_pieces (e : Edge) (ε : ℝ) :
    (C.shiftedEdgeChain e ε).pieces=V.pieces e+2 := by
  simp only [shiftedEdgeChain,PolygonalChain.pieces_join,connectorChain,
    PolygonalChain.pieces_single,shiftedTrackChain,PolygonalChain.reverse]
  omega

theorem shiftedEdgeChain_intersection_right (e : Edge) (ε : ℝ)
    (w : ℕ → Plane) (k : ℕ) :
    polygonIntersection w (C.shiftedEdgeChain e ε).vertices k (C.shiftedEdgeChain e ε).pieces =
      polygonIntersection w (C.connectorChain ((graph.src e)) (V.leftIncident e) ε).vertices k 1 +
      polygonIntersection w (shiftedTrack (V.vertices e) (V.pieces e) ε) k (V.pieces e) -
      polygonIntersection w (C.connectorChain ((graph.dst e)) (V.rightIncident e) ε).vertices k 1 := by
  unfold shiftedEdgeChain
  rw [PolygonalChain.intersection_join_right,PolygonalChain.intersection_join_right,
    PolygonalChain.intersection_reverse_right]
  rfl

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! Actual polygonal realizations of the two orientations of every graph edge. -/
noncomputable section
open Zarankiewicz
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

def dartTrackChain (d : OrientedDart graph) :
    PolygonalChain Set.univ (V.spokePort d.fst (dartSourceIncident d))
      (V.spokePort d.snd (dartTargetIncident d)) := by
  rcases d with ⟨e,b⟩
  cases b
  · exact (V.trackChain e).reverse.castEndpoints
      (by simp [spokePort,drawingSpokePort,dartSourceIncident,OrientedDart.fst,
        endPort,(graph.loopless e).symm])
      (by simp [spokePort,drawingSpokePort,dartTargetIncident,OrientedDart.snd,startPort])
  · exact (V.trackChain e).castEndpoints
      (by simp [spokePort,drawingSpokePort,dartSourceIncident,OrientedDart.fst,startPort])
      (by simp [spokePort,drawingSpokePort,dartTargetIncident,OrientedDart.snd,
        endPort,(graph.loopless e).symm])

theorem dartTrackChain_forward_vertices (e : Edge) :
    (V.dartTrackChain (forwardDart graph e)).vertices = V.vertices e := rfl

theorem dartTrackChain_backward_vertices (e : Edge) :
    (V.dartTrackChain (backwardDart graph e)).vertices =
      reversedSequence (V.vertices e) (V.pieces e) := rfl

theorem dartTrackChain_pieces (d : OrientedDart graph) :
    (V.dartTrackChain d).pieces = V.pieces d.edge := by
  rcases orientedDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩ <;> rfl

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

def shiftedDartChain (d : OrientedDart graph) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort d.fst (dartSourceIncident d) ε)
      (C.shiftedPort d.snd (dartTargetIncident d) ε) := by
  rcases d with ⟨e,b⟩
  cases b
  · exact (C.shiftedEdgeChain e ε).reverse.castEndpoints rfl rfl
  · exact (C.shiftedEdgeChain e ε).castEndpoints rfl rfl

theorem shiftedDartChain_forward_vertices (e : Edge) (ε : ℝ) :
    (C.shiftedDartChain (forwardDart graph e) ε).vertices = (C.shiftedEdgeChain e ε).vertices := rfl

theorem shiftedDartChain_backward_vertices (e : Edge) (ε : ℝ) :
    (C.shiftedDartChain (backwardDart graph e) ε).vertices =
      reversedSequence (C.shiftedEdgeChain e ε).vertices (C.shiftedEdgeChain e ε).pieces := rfl

theorem shiftedDartChain_pieces (d : OrientedDart graph) (ε : ℝ) :
    (C.shiftedDartChain d ε).pieces = (C.shiftedEdgeChain d.edge ε).pieces := by
  rcases orientedDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩ <;> rfl

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! Actual closed polygonal realizations of cyclic graph darts, with a chord at every vertex passage. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry

def incidentCast {j k : Vertex} (h : j=k) (e : IncidentEdges graph j) : IncidentEdges graph k :=
  ⟨e.val,by simpa only [← h] using e.property⟩

theorem incidentCast_val {j k : Vertex} (h : j=k) (e : IncidentEdges graph j) :
    (incidentCast h e).val=e.val := rfl

def dartPassageNext (d : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ) : IncidentEdges graph (d i).snd :=
  incidentCast (hd i).symm (dartSourceIncident (d (i+1)))

theorem dartPassage_ne (d : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ)
    (hne : OrientedDart.edge (d (i+1)) ≠ OrientedDart.edge (d i)) :
    dartTargetIncident (d i) ≠ dartPassageNext d hd i := by
  intro he
  exact hne (congrArg Subtype.val he).symm

namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem spokePort_cast {j k : Vertex} (h : j=k) (e : IncidentEdges graph j) :
    V.spokePort k (incidentCast h e)=V.spokePort j e := by subst k; rfl

def dartCycleVertex (d : ℕ → OrientedDart graph) (i : ℕ) : Plane :=
  V.spokePort (d i).fst (dartSourceIncident (d i))

def dartCycleBlock (d : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ) :
    PolygonalChain Set.univ (V.dartCycleVertex d i) (V.dartCycleVertex d (i+1)) :=
  ((V.dartTrackChain (d i)).join
    (V.chordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i))).castEndpoints
      rfl (V.spokePort_cast (hd i).symm _).symm

def dartCycleChain (d : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (N : ℕ) (hN : d N=d 0) :
    PolygonalChain Set.univ (V.dartCycleVertex d 0) (V.dartCycleVertex d 0) :=
  (finitePolygonalChain Set.univ (V.dartCycleVertex d) (Set.mem_univ _) (V.dartCycleBlock d hd) N).castEndpoints
    rfl (congrArg (fun a : OrientedDart graph => V.spokePort a.fst (dartSourceIncident a)) hN.symm)

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D} (C : TruncatedSpokeCoordinates V)

theorem shiftedPort_cast {j k : Vertex} (h : j=k) (e : IncidentEdges graph j) (ε : ℝ) :
    C.shiftedPort k (incidentCast h e) ε=C.shiftedPort j e ε := by subst k; rfl

def shiftedCycleVertex (d : ℕ → OrientedDart graph) (ε : ℝ) (i : ℕ) : Plane :=
  C.shiftedPort (d i).fst (dartSourceIncident (d i)) ε

def shiftedCycleBlock (d : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (ε : ℝ) (i : ℕ) :
    PolygonalChain Set.univ (C.shiftedCycleVertex d ε i) (C.shiftedCycleVertex d ε (i+1)) :=
  ((C.shiftedDartChain (d i) ε).join
    (C.shiftedChordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i) ε)).castEndpoints
      rfl (C.shiftedPort_cast (hd i).symm _ ε).symm

def shiftedCycleChain (d : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (N : ℕ) (hN : d N=d 0) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedCycleVertex d ε 0) (C.shiftedCycleVertex d ε 0) :=
  (finitePolygonalChain Set.univ (C.shiftedCycleVertex d ε) (Set.mem_univ _) (C.shiftedCycleBlock d hd ε) N).castEndpoints
    rfl (congrArg (fun a : OrientedDart graph => C.shiftedPort a.fst (dartSourceIncident a) ε) hN.symm)

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! Endpoint pairings at actual vertex-circle passages. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def vertexChordPairing (j k : Vertex) (a b : IncidentEdges graph j) (c d : IncidentEdges graph k) : ℝ :=
  if h : k=j then chordEndpointPairing (C.node j a) (C.node j b)
    (C.node j (incidentCast h c)) (C.node j (incidentCast h d)) else 0

def passagePairing (d f : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (i j : ℕ) : ℝ :=
  C.vertexChordPairing (d i).snd (f j).snd (dartTargetIncident (d i)) (dartPassageNext d hd i)
    (dartTargetIncident (f j)) (dartPassageNext f hf j)

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Fixed vertex half-order kernels on actual incident edge flags. -/
noncomputable section
open Zarankiewicz
open scoped Classical
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

abbrev IncidentFlag (graph : Paper170.Graph Vertex Edge) := (j : Vertex) × IncidentEdges graph j

def dartSourceFlag (d : OrientedDart graph) : IncidentFlag graph :=
  ⟨d.fst,dartSourceIncident d⟩

def dartTargetFlag (d : OrientedDart graph) : IncidentFlag graph :=
  ⟨d.snd,dartTargetIncident d⟩

theorem incidentCast_refl {j : Vertex} (e : IncidentEdges graph j) :
    incidentCast (rfl : j=j) e=e := Subtype.ext rfl

theorem incidentFlag_cast {j k : Vertex} (h : j=k) (e : IncidentEdges graph j) :
    (⟨k,incidentCast h e⟩ : IncidentFlag graph)=⟨j,e⟩ := by
  subst k
  rw [incidentCast_refl]

theorem dartPassageNext_flag (d : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ) :
    (⟨(d i).snd,dartPassageNext d hd i⟩ : IncidentFlag graph)=dartSourceFlag (d (i+1)) :=
  incidentFlag_cast (hd i).symm _

namespace TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def flagPairing (a b : IncidentFlag graph) : ℝ :=
  if h : b.1=a.1 then orderSign (C.node a.1 a.2) (C.node a.1 (incidentCast h b.2))/2 else 0

theorem vertexChordPairing_flags (j k : Vertex)
    (a b : IncidentEdges graph j) (c d : IncidentEdges graph k) :
    C.vertexChordPairing j k a b c d=
      C.flagPairing ⟨j,a⟩ ⟨k,c⟩-C.flagPairing ⟨j,a⟩ ⟨k,d⟩-
        C.flagPairing ⟨j,b⟩ ⟨k,c⟩+C.flagPairing ⟨j,b⟩ ⟨k,d⟩ := by
  by_cases h : k=j
  · subst k
    simp only [vertexChordPairing,flagPairing,dite_eq_left rfl,incidentCast_refl,chordEndpointPairing,dite_true]
    ring
  · simp only [vertexChordPairing,flagPairing,dite_eq_right h,sub_zero,add_zero]

theorem passagePairing_flags (d f : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst) (i j : ℕ) :
    C.passagePairing d f hd hf i j=
      C.flagPairing (dartTargetFlag (d i)) (dartTargetFlag (f j))-
        C.flagPairing (dartTargetFlag (d i)) (dartSourceFlag (f (j+1)))-
        C.flagPairing (dartSourceFlag (d (i+1))) (dartTargetFlag (f j))+
        C.flagPairing (dartSourceFlag (d (i+1))) (dartSourceFlag (f (j+1))) := by
  rw [passagePairing,C.vertexChordPairing_flags,dartPassageNext_flag,dartPassageNext_flag]
  rfl

def edgeEndpointPairing (e f : Edge) : ℝ :=
  C.flagPairing (dartTargetFlag (forwardDart graph e)) (dartTargetFlag (forwardDart graph f))-
    C.flagPairing (dartTargetFlag (forwardDart graph e)) (dartSourceFlag (forwardDart graph f))-
    C.flagPairing (dartSourceFlag (forwardDart graph e)) (dartTargetFlag (forwardDart graph f))+
    C.flagPairing (dartSourceFlag (forwardDart graph e)) (dartSourceFlag (forwardDart graph f))

theorem dart_endpoint_pairing (a b : OrientedDart graph) :
    C.flagPairing (dartTargetFlag a) (dartTargetFlag b)-
      C.flagPairing (dartTargetFlag a) (dartSourceFlag b)-
      C.flagPairing (dartSourceFlag a) (dartTargetFlag b)+
      C.flagPairing (dartSourceFlag a) (dartSourceFlag b)=
        dartSign a*dartSign b*C.edgeEndpointPairing a.edge b.edge := by
  rcases a with ⟨e,a⟩
  rcases b with ⟨f,b⟩
  cases a <;> cases b <;>
    simp [dartSign,edgeEndpointPairing,forwardDart,dartSourceFlag,dartTargetFlag,
      dartSourceIncident,dartTargetIncident,OrientedDart.fst,OrientedDart.snd]
  all_goals ring

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

end OAI
