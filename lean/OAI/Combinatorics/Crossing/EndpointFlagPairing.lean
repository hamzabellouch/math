import OAI.Combinatorics.Crossing.GlobalCycleAveraging

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

abbrev IncidentFlag (m n : ℕ) := (j : BipartiteVertex m n) × IncidentEdges j

def dartSourceFlag (d : (completeBipartite m n).Dart) : IncidentFlag m n :=
  ⟨d.fst,dartSourceIncident d⟩

def dartTargetFlag (d : (completeBipartite m n).Dart) : IncidentFlag m n :=
  ⟨d.snd,dartTargetIncident d⟩

theorem incidentCast_refl {j : BipartiteVertex m n} (e : IncidentEdges j) :
    incidentCast (rfl : j=j) e=e := Subtype.ext rfl

theorem incidentFlag_cast {j k : BipartiteVertex m n} (h : j=k) (e : IncidentEdges j) :
    (⟨k,incidentCast h e⟩ : IncidentFlag m n)=⟨j,e⟩ := by
  subst k
  rw [incidentCast_refl]

theorem dartPassageNext_flag (d : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ) :
    (⟨(d i).snd,dartPassageNext d hd i⟩ : IncidentFlag m n)=dartSourceFlag (d (i+1)) :=
  incidentFlag_cast (hd i).symm _

namespace TruncatedSpokeCoordinates
variable {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def flagPairing (a b : IncidentFlag m n) : ℝ :=
  if h : b.1=a.1 then orderSign (C.node a.1 a.2) (C.node a.1 (incidentCast h b.2))/2 else 0

theorem vertexChordPairing_flags (j k : BipartiteVertex m n)
    (a b : IncidentEdges j) (c d : IncidentEdges k) :
    C.vertexChordPairing j k a b c d=
      C.flagPairing ⟨j,a⟩ ⟨k,c⟩-C.flagPairing ⟨j,a⟩ ⟨k,d⟩-
        C.flagPairing ⟨j,b⟩ ⟨k,c⟩+C.flagPairing ⟨j,b⟩ ⟨k,d⟩ := by
  by_cases h : k=j
  · subst k
    simp only [vertexChordPairing,flagPairing,dite_eq_left rfl,incidentCast_refl,chordEndpointPairing,dite_true]
    ring
  · simp only [vertexChordPairing,flagPairing,dite_eq_right h,sub_zero,add_zero]

theorem passagePairing_flags (d f : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst) (i j : ℕ) :
    C.passagePairing d f hd hf i j=
      C.flagPairing (dartTargetFlag (d i)) (dartTargetFlag (f j))-
        C.flagPairing (dartTargetFlag (d i)) (dartSourceFlag (f (j+1)))-
        C.flagPairing (dartSourceFlag (d (i+1))) (dartTargetFlag (f j))+
        C.flagPairing (dartSourceFlag (d (i+1))) (dartSourceFlag (f (j+1))) := by
  rw [passagePairing,C.vertexChordPairing_flags,dartPassageNext_flag,dartPassageNext_flag]
  rfl

def edgeEndpointPairing (e f : BipartiteEdge m n) : ℝ :=
  C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))+
    C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))

theorem flagPairing_source_target (e f : BipartiteEdge m n) :
    C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))=0 := by
  simp [flagPairing,dartSourceFlag,dartTargetFlag,forwardBipartiteDart]

theorem flagPairing_target_source (e f : BipartiteEdge m n) :
    C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))=0 := by
  simp [flagPairing,dartSourceFlag,dartTargetFlag,forwardBipartiteDart]

theorem dart_endpoint_pairing (a b : (completeBipartite m n).Dart) :
    C.flagPairing (dartTargetFlag a) (dartTargetFlag b)-
      C.flagPairing (dartTargetFlag a) (dartSourceFlag b)-
      C.flagPairing (dartSourceFlag a) (dartTargetFlag b)+
      C.flagPairing (dartSourceFlag a) (dartSourceFlag b)=
        bipartiteDartSign a*bipartiteDartSign b*C.edgeEndpointPairing (bipartiteDartEdge a) (bipartiteDartEdge b) := by
  rcases bipartiteDart_cases a with ⟨e,rfl⟩ | ⟨e,rfl⟩ <;>
    rcases bipartiteDart_cases b with ⟨f,rfl⟩ | ⟨f,rfl⟩
  all_goals
    change _ = _*_*C.edgeEndpointPairing e f
    have hST := C.flagPairing_source_target e f
    have hTS := C.flagPairing_target_source e f
    simp only [edgeEndpointPairing] at *
    change C.flagPairing _ _=0 at hST hTS
  · rw [hST,hTS]
    change _ = 1*1*_
    ring
  · change C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))-
      C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))-
      C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))+
      C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))=1*(-1)*_
    rw [hST,hTS]
    ring
  · change C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))-
      C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))-
      C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))+
      C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))=(-1)*1*_
    rw [hST,hTS]
    ring
  · change C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))-
      C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))-
      C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))+
      C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))=(-1)*(-1)*_
    rw [hST,hTS]
    ring

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
