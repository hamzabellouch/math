import OAI.Combinatorics.Crossing.GlobalCycleIntersection

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def vertexChordPairing (j k : BipartiteVertex m n) (a b : IncidentEdges j) (c d : IncidentEdges k) : ℝ :=
  if h : k=j then chordEndpointPairing (C.node j a) (C.node j b)
    (C.node j (incidentCast h c)) (C.node j (incidentCast h d)) else 0

def passagePairing (d f : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (i j : ℕ) : ℝ :=
  C.vertexChordPairing (d i).snd (f j).snd (dartTargetIncident (d i)) (dartPassageNext d hd i)
    (dartTargetIncident (f j)) (dartPassageNext f hf j)

theorem exists_vertex_pairing_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ j k (a b : IncidentEdges j) (c d : IncidentEdges k), a ≠ b → c ≠ d →
        (polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d t).vertices 1 1+
          polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d (-t)).vertices 1 1)/2=
            C.vertexChordPairing j k a b c d := by
  obtain ⟨δ,hδ,-,hzero,havg⟩ := C.exists_vertex_chord_chain_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro t ht hs j k a b c d hab hcd
  by_cases h : k=j
  · subst k
    have hc : incidentCast (rfl : j=j) c=c := Subtype.ext rfl
    have hd : incidentCast (rfl : j=j) d=d := Subtype.ext rfl
    rw [vertexChordPairing,dite_eq_left rfl,hc,hd]
    exact havg t ht hs j a b c d hab hcd
  · have hzplus := hzero t (ne_of_gt ht) (by simpa only [abs_of_pos ht] using hs) j k (Ne.symm h) a b c d
    have hzminus := hzero (-t) (neg_ne_zero.mpr (ne_of_gt ht)) (by simpa only [abs_neg,abs_of_pos ht] using hs)
      j k (Ne.symm h) a b c d
    rw [hzplus,hzminus,zero_add,zero_div]
    simp only [vertexChordPairing,dite_eq_right h]

theorem exists_passage_pairing_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ (d f : ℕ → (completeBipartite m n).Dart)
        (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst) (i j : ℕ),
      bipartiteDartEdge (d (i+1)) ≠ bipartiteDartEdge (d i) →
      bipartiteDartEdge (f (j+1)) ≠ bipartiteDartEdge (f j) →
      (C.passageIntersection d f hd hf i j t+C.passageIntersection d f hd hf i j (-t))/2=
        C.passagePairing d f hd hf i j := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_vertex_pairing_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro t ht hs d f hd hf i j hi hj
  exact hh t ht hs _ _ _ _ _ _ (dartPassage_ne d hd i hi) (dartPassage_ne f hf j hj)

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
