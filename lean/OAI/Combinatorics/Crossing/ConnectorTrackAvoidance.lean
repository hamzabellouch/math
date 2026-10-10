import OAI.Combinatorics.Crossing.ConnectorSupportingLines

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
open scoped Topology
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_nonincident_connector_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ j (f : IncidentEdges j) e (i : Fin (V.pieces e)),
      ¬ (e=f.val ∧ i.val=V.spokeIndex j f) →
      ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
        (C.shiftedPort j f ε) (C.tangentPort j f ε) := by
  classical
  let Bad := Σ j : BipartiteVertex m n, Σ f : IncidentEdges j, Σ e : BipartiteEdge m n,
    {i : Fin (V.pieces e) // ¬ (e=f.val ∧ i.val=V.spokeIndex j f)}
  have hnot (b : Bad) : ¬ ClosedSegmentsMeet
      (V.vertices b.2.2.1 b.2.2.2.val.val) (V.vertices b.2.2.1 (b.2.2.2.val.val+1))
      (V.spokePort b.1 b.2.1) (V.spokePort b.1 b.2.1) := by
    rintro ⟨s,hs,t,ht,he⟩
    have he0 : segmentPoint (V.spokePort b.1 b.2.1) (V.spokePort b.1 b.2.1) t=V.spokePort b.1 b.2.1 := by
      unfold segmentPoint
      rw [← add_smul]
      simp
    rw [he0] at he
    have hx : V.spokePort b.1 b.2.1 ∈
        segment ℝ (V.vertices b.2.2.1 b.2.2.2.val.val) (V.vertices b.2.2.1 (b.2.2.2.val.val+1)) := by
      rw [← Path.range_segment]
      refine ⟨⟨s,hs⟩,?_⟩
      simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he
    exact b.2.2.2.property (V.spokePort_piece_unique hnorm b.1 b.2.1 b.2.2.1 b.2.2.2.val hx)
  have hevent (b : Bad) := eventually_moving_disjoint_segments
    (V.vertices b.2.2.1 b.2.2.2.val.val) (V.vertices b.2.2.1 (b.2.2.2.val.val+1))
    (V.spokePort b.1 b.2.1) (V.spokePort b.1 b.2.1) (C.shiftedPort b.1 b.2.1) (C.tangentPort b.1 b.2.1)
    (C.continuous_shiftedPort b.1 b.2.1).continuousAt (C.continuous_tangentPort b.1 b.2.1).continuousAt
    (C.shiftedPort_zero b.1 b.2.1) (C.tangentPort_zero b.1 b.2.1) (hnot b)
  have hex (b : Bad) := Metric.eventually_nhds_iff.mp (hevent b)
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun b _ => hpos b)
  refine ⟨δ,hδ,?_⟩
  intro ε hε j f e i hi
  exact hprop ⟨j,f,e,⟨i,hi⟩⟩ (by simpa [Real.dist_eq] using hε.trans (hbound ⟨j,f,e,⟨i,hi⟩⟩ (Finset.mem_univ _)))

theorem exists_all_connector_track_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j (f : IncidentEdges j) e (i : Fin (V.pieces e)),
      ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
        (C.shiftedPort j f ε) (C.tangentPort j f ε) := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_nonincident_connector_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall j f e i
  by_cases hi : e=f.val ∧ i.val=V.spokeIndex j f
  · rcases hi with ⟨rfl,hi⟩
    simpa only [hi] using C.connector_avoids_incident_piece j f ε hε
  · exact hh ε hsmall j f e i hi

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
