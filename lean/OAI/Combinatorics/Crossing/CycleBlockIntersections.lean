import OAI.Combinatorics.Crossing.DartCyclePaths
import OAI.Combinatorics.Crossing.DartPairIntersections
import OAI.Combinatorics.Crossing.VertexChordIntersections

namespace OAI

noncomputable section
namespace Zarankiewicz

namespace PolygonalChain
variable {O T : Set Plane} {a b c d e f : Plane}

theorem intersection_join_join (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (R : PolygonalChain T d e) (S : PolygonalChain T e f) :
    polygonIntersection (P.join Q).vertices (R.join S).vertices (P.join Q).pieces (R.join S).pieces=
      polygonIntersection P.vertices R.vertices P.pieces R.pieces+
      polygonIntersection P.vertices S.vertices P.pieces S.pieces+
      polygonIntersection Q.vertices R.vertices Q.pieces R.pieces+
      polygonIntersection Q.vertices S.vertices Q.pieces S.pieces := by
  rw [intersection_join_left,intersection_join_right,intersection_join_right]
  ring

theorem transverse_join_join (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (R : PolygonalChain T d e) (S : PolygonalChain T e f)
    (hPR : P.Transverse R) (hPS : P.Transverse S) (hQR : Q.Transverse R) (hQS : Q.Transverse S) :
    (P.join Q).Transverse (R.join S) :=
  P.transverse_join_left Q (R.join S)
    (R.transverse_join_right S P hPR hPS) (R.transverse_join_right S Q hQR hQS)

end PolygonalChain
namespace TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def passageIntersection (d f : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (i j : ℕ) (ε : ℝ) : ℝ :=
  polygonIntersection (V.chordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i)).vertices
    (C.shiftedChordChain (f j).snd (dartTargetIncident (f j)) (dartPassageNext f hf j) ε).vertices 1 1

theorem exists_cycle_block_radius (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ →
      ∀ (d f : ℕ → (completeBipartite m n).Dart)
        (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst) (i j : ℕ),
      bipartiteDartEdge (d (i+1)) ≠ bipartiteDartEdge (d i) →
      bipartiteDartEdge (f (j+1)) ≠ bipartiteDartEdge (f j) →
      (V.dartCycleBlock d hd i).Transverse (C.shiftedCycleBlock f hf ε j) ∧
      polygonIntersection (V.dartCycleBlock d hd i).vertices (C.shiftedCycleBlock f hf ε j).vertices
        (V.dartCycleBlock d hd i).pieces (C.shiftedCycleBlock f hf ε j).pieces=
          bipartiteDartSign (d i)*bipartiteDartSign (f j)*
            V.signedIntersection (bipartiteDartEdge (d i)) (bipartiteDartEdge (f j))+
              C.passageIntersection d f hd hf i j ε := by
  obtain ⟨δ₀,hδ₀,h₀⟩ := C.exists_dart_intersection_radius hnorm hstraight htrans
  obtain ⟨δ₁,hδ₁,h₁,-,-⟩ := C.exists_vertex_chord_chain_radius hnorm
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro ε hε hs d f hd hf i j hdi hfj
  obtain ⟨hdd,hcd,hdc⟩ := h₀ ε hε (hs.trans_le (min_le_left _ _))
  have hcc := h₁ ε hε (hs.trans_le (min_le_right _ _))
    (d i).snd (f j).snd (dartTargetIncident (d i)) (dartPassageNext d hd i)
      (dartTargetIncident (f j)) (dartPassageNext f hf j)
        (dartPassage_ne d hd i hdi) (dartPassage_ne f hf j hfj)
  obtain ⟨hDD,hDI⟩ := hdd (d i) (f j)
  obtain ⟨hCD,hCI⟩ := hcd (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i) (f j)
  obtain ⟨hDC,hIC⟩ := hdc (f j).snd (dartTargetIncident (f j)) (dartPassageNext f hf j) (d i)
  constructor
  · exact PolygonalChain.transverse_join_join _ _ _ _ hDD hDC hCD hcc
  · change polygonIntersection
      ((V.dartTrackChain (d i)).join (V.chordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i))).vertices
      ((C.shiftedDartChain (f j) ε).join (C.shiftedChordChain (f j).snd (dartTargetIncident (f j)) (dartPassageNext f hf j) ε)).vertices
      ((V.dartTrackChain (d i)).join (V.chordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i))).pieces
      ((C.shiftedDartChain (f j) ε).join (C.shiftedChordChain (f j).snd (dartTargetIncident (f j)) (dartPassageNext f hf j) ε)).pieces=_
    rw [PolygonalChain.intersection_join_join,hDI,hIC,hCI,add_zero,add_zero]
    rfl

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
