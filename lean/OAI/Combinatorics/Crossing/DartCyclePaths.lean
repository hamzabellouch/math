import OAI.Combinatorics.Crossing.CyclicWalkDarts
import OAI.Combinatorics.Crossing.DartPathRealizations

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def incidentCast {j k : BipartiteVertex m n} (h : j=k) (e : IncidentEdges j) : IncidentEdges k :=
  ⟨e.val,by simpa only [← h] using e.property⟩

theorem incidentCast_val {j k : BipartiteVertex m n} (h : j=k) (e : IncidentEdges j) :
    (incidentCast h e).val=e.val := rfl

def dartPassageNext (d : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ) : IncidentEdges (d i).snd :=
  incidentCast (hd i).symm (dartSourceIncident (d (i+1)))

theorem dartPassage_ne (d : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ)
    (hne : bipartiteDartEdge (d (i+1)) ≠ bipartiteDartEdge (d i)) :
    dartTargetIncident (d i) ≠ dartPassageNext d hd i := by
  intro he
  exact hne (congrArg Subtype.val he).symm

namespace VertexTruncation
variable {D : ContinuousDrawing m n} (V : VertexTruncation D)

theorem spokePort_cast {j k : BipartiteVertex m n} (h : j=k) (e : IncidentEdges j) :
    V.spokePort k (incidentCast h e)=V.spokePort j e := by subst k; rfl

def dartCycleVertex (d : ℕ → (completeBipartite m n).Dart) (i : ℕ) : Plane :=
  V.spokePort (d i).fst (dartSourceIncident (d i))

def dartCycleBlock (d : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ) :
    PolygonalChain Set.univ (V.dartCycleVertex d i) (V.dartCycleVertex d (i+1)) :=
  ((V.dartTrackChain (d i)).join
    (V.chordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i))).castEndpoints
      rfl (V.spokePort_cast (hd i).symm _).symm

def dartCycleChain (d : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (N : ℕ) (hN : d N=d 0) :
    PolygonalChain Set.univ (V.dartCycleVertex d 0) (V.dartCycleVertex d 0) :=
  (finitePolygonalChain Set.univ (V.dartCycleVertex d) (Set.mem_univ _) (V.dartCycleBlock d hd) N).castEndpoints
    rfl (congrArg (fun a : (completeBipartite m n).Dart => V.spokePort a.fst (dartSourceIncident a)) hN.symm)

def graphCycleChain {u : BipartiteVertex m n} (p : (completeBipartite m n).Walk u u)
    (hp : 0 < p.length) : PolygonalChain Set.univ
      (V.dartCycleVertex (cyclicWalkDart p hp) 0) (V.dartCycleVertex (cyclicWalkDart p hp) 0) :=
  V.dartCycleChain (cyclicWalkDart p hp) (cyclicWalkDart_seam p hp) p.length (cyclicWalkDart_period p hp)

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {D : ContinuousDrawing m n} {V : VertexTruncation D} (C : TruncatedSpokeCoordinates V)

theorem shiftedPort_cast {j k : BipartiteVertex m n} (h : j=k) (e : IncidentEdges j) (ε : ℝ) :
    C.shiftedPort k (incidentCast h e) ε=C.shiftedPort j e ε := by subst k; rfl

def shiftedCycleVertex (d : ℕ → (completeBipartite m n).Dart) (ε : ℝ) (i : ℕ) : Plane :=
  C.shiftedPort (d i).fst (dartSourceIncident (d i)) ε

def shiftedCycleBlock (d : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (ε : ℝ) (i : ℕ) :
    PolygonalChain Set.univ (C.shiftedCycleVertex d ε i) (C.shiftedCycleVertex d ε (i+1)) :=
  ((C.shiftedDartChain (d i) ε).join
    (C.shiftedChordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i) ε)).castEndpoints
      rfl (C.shiftedPort_cast (hd i).symm _ ε).symm

def shiftedCycleChain (d : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (N : ℕ) (hN : d N=d 0) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedCycleVertex d ε 0) (C.shiftedCycleVertex d ε 0) :=
  (finitePolygonalChain Set.univ (C.shiftedCycleVertex d ε) (Set.mem_univ _) (C.shiftedCycleBlock d hd ε) N).castEndpoints
    rfl (congrArg (fun a : (completeBipartite m n).Dart => C.shiftedPort a.fst (dartSourceIncident a) ε) hN.symm)

def shiftedGraphCycleChain {u : BipartiteVertex m n} (p : (completeBipartite m n).Walk u u)
    (hp : 0 < p.length) (ε : ℝ) : PolygonalChain Set.univ
      (C.shiftedCycleVertex (cyclicWalkDart p hp) ε 0) (C.shiftedCycleVertex (cyclicWalkDart p hp) ε 0) :=
  C.shiftedCycleChain (cyclicWalkDart p hp) (cyclicWalkDart_seam p hp) p.length (cyclicWalkDart_period p hp) ε

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
