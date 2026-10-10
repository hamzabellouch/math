import OAI.Combinatorics.CompleteCrossing.RadialTracks
import OAI.Combinatorics.Crossing.DiskSegments
import OAI.Combinatorics.Crossing.FiniteScaledRadius
import OAI.Combinatorics.Crossing.RoundCircleChords
import OAI.Combinatorics.Crossing.RoundDiskChords
import OAI.Combinatorics.Crossing.SegmentTraversalReversal

namespace OAI

/-! Uniform spoke radii, vertex chords, and separation from exterior tracks. -/

section

/-! Common physical radii for every vertex of the actual drawing, fixed before any cycle choices. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem port_injective (C : TruncatedSpokeCoordinates V) (j : Vertex) : Function.Injective (V.spokePort j) := by
  intro e f he
  apply C.node_injective j
  apply circlePoint_injective
  apply similarityPoint_injective (D.vertex j) (C.frame j) (C.frame_ne_zero j)
  simpa only [C.point_eq] using he

theorem exists_uniform_endpoint_radius [Fintype Vertex] [Fintype Edge] :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j : Vertex,
      (∀ e f : IncidentEdges graph j, V.spokePort j e ≠ C.shiftedPort j f ε) ∧
      Function.Injective (fun e : IncidentEdges graph j => C.shiftedPort j e ε) := by
  classical
  choose radius hpos hprop using C.exists_endpoint_separation_radius
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun j _ => hpos j)
  exact ⟨δ,hδ,fun ε hε hsmall j => hprop j ε hε (hsmall.trans (hbound j (Finset.mem_univ _)))⟩

theorem exists_uniform_scale_radius [Fintype Vertex] [Fintype Edge] (_C : TruncatedSpokeCoordinates V) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ j (e : IncidentEdges graph j), |V.spokeScale j e*ε|<1 := by
  let Spoke := Σ j : Vertex, IncidentEdges graph j
  obtain ⟨δ,hδ,hbound⟩ := finite_scaled_radius
    (fun s : Spoke => V.spokeScale s.1 s.2) (fun _ => (1 : ℝ)) (by intro s; norm_num)
  exact ⟨δ,hδ,fun ε hε j e => hbound ε hε ⟨j,e⟩⟩

theorem exists_uniform_average_radius [Fintype Vertex] [Fintype Edge] :
    ∃ δ : ℝ, 0<δ ∧ ∀ t : ℝ, 0<t → t<δ → ∀ j (a b c d : IncidentEdges graph j),
      a ≠ b → c ≠ d →
      (segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c t) (C.shiftedPort j d t)+
        segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c (-t)) (C.shiftedPort j d (-t)))/2 =
      chordEndpointPairing (C.node j a) (C.node j b) (C.node j c) (C.node j d) := by
  classical
  choose radius hpos hprop using C.exists_vertex_average_radius
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun j _ => hpos j)
  exact ⟨δ,hδ,fun t ht hsmall j => hprop j t ht (hsmall.trans (hbound j (Finset.mem_univ _)))⟩

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Actual local chords have transverse meetings and avoid the exterior connector seams. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem shifted_chords_transverse (j : Vertex) (a b c d : IncidentEdges graph j)
    (ε : ℝ) (hsmall : ∀ e : IncidentEdges graph j, |V.spokeScale j e*ε|≤1)
    (hsep : ∀ e f : IncidentEdges graph j, V.spokePort j e ≠ C.shiftedPort j f ε)
    (hinj : Function.Injective (fun e : IncidentEdges graph j => C.shiftedPort j e ε))
    (hab : a ≠ b) (hcd : c ≠ d) :
    SegmentPairTransverse (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c ε) (C.shiftedPort j d ε) :=
  round_circle_chords_transverse (D.vertex j) _ _ _ _ V.radius
    (V.spokePort_circle j a) (V.spokePort_circle j b)
    (C.shiftedPort_circle j c ε (hsmall c)) (C.shiftedPort_circle j d ε (hsmall d))
    ((C.port_injective j).ne hab) (hinj.ne hcd) (hsep a c) (hsep a d) (hsep b c) (hsep b d)

theorem chord_connector_disjoint (j : Vertex) (a b e : IncidentEdges graph j)
    (ε : ℝ) (hne : ε ≠ 0) (hsmall : |V.spokeScale j e*ε|<1) (hab : a ≠ b)
    (ha : V.spokePort j a ≠ C.shiftedPort j e ε) (hb : V.spokePort j b ≠ C.shiftedPort j e ε) :
    ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j e ε) (C.tangentPort j e ε) := by
  have hunit (f : IncidentEdges graph j) : squaredLength (circlePoint (C.node j f))=1 := circlePoint_on_unit_circle _
  have haq : circlePoint (C.node j a) ≠ circleOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε) := by
    intro he
    apply ha
    rw [← C.point_eq j a]
    exact congrArg (similarityPoint (D.vertex j) (C.frame j)) he
  have hbq : circlePoint (C.node j b) ≠ circleOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε) := by
    intro he
    apply hb
    rw [← C.point_eq j b]
    exact congrArg (similarityPoint (D.vertex j) (C.frame j)) he
  have hd := unit_chord_connector_disjoint (circlePoint (C.node j a)) (circlePoint (C.node j b))
    (circlePoint (C.node j e)) (hunit a) (hunit b) (hunit e)
    (fun he => hab (C.node_injective j (circlePoint_injective he)))
    (V.spokeScale j e*ε) hsmall (mul_ne_zero (V.spokeScale_ne_zero j e) hne) haq hbq
  rintro ⟨s,hs,t,ht,he⟩
  apply hd
  refine ⟨s,hs,t,ht,?_⟩
  apply similarityPoint_injective (D.vertex j) (C.frame j) (C.frame_ne_zero j)
  simpa only [similarityPoint_segment,C.point_eq,← C.tangentPort_eq,shiftedPort] using he

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Original exterior tracks avoid every shifted vertex chord, including at boundary seams. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem track_in_disk_is_port (j : Vertex) (e : Edge) (x : Plane)
    (hx : x ∈ Set.range (V.path e)) (hmem : x ∈ closedRoundDisk (D.vertex j) V.radius) :
    ∃ f : IncidentEdges graph j, x=V.spokePort j f := by
  rcases V.vertex_disk_cases j e x hx with ⟨hj,he⟩ | ⟨hj,he⟩ | hout
  · refine ⟨⟨e,Or.inl hj⟩,?_⟩
    simpa only [spokePort,drawingSpokePort,ite_eq_left hj,startPort] using he
  · have hnot : j ≠ (graph.src e) := by
      intro hh
      exact (graph.loopless e) (hh.symm.trans hj)
    refine ⟨⟨e,Or.inr hj⟩,?_⟩
    simpa only [spokePort,drawingSpokePort,ite_eq_right hnot,endPort] using he
  · exact False.elim (not_lt_of_ge hmem hout)

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem track_shifted_chord_disjoint (j : Vertex) (c d : IncidentEdges graph j)
    (ε : ℝ) (hc : |V.spokeScale j c*ε|≤1) (hd : |V.spokeScale j d*ε|≤1)
    (hsep : ∀ f g : IncidentEdges graph j, V.spokePort j f ≠ C.shiftedPort j g ε)
    (e : Edge) (i : Fin (V.pieces e)) :
    ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
      (C.shiftedPort j c ε) (C.shiftedPort j d ε) := by
  intro hmeet
  obtain ⟨x,hx,hy⟩ := (closedSegmentsMeet_iff_nonempty_inter _ _ _ _).mp hmeet
  have hcirclec := C.shiftedPort_circle j c ε hc
  have hcircled := C.shiftedPort_circle j d ε hd
  have hmem := round_chord_subset_closed_disk (D.vertex j) _ _ V.radius hcirclec hcircled hy
  obtain ⟨f,hf⟩ := V.track_in_disk_is_port j e x (V.piece_subset_range e i.val i.isLt hx) hmem
  have hboundary : squaredLength (x-D.vertex j)=V.radius^2 := by rw [hf,V.spokePort_circle]
  rcases round_chord_boundary_endpoints (D.vertex j) _ _ x V.radius hcirclec hcircled hy hboundary with h | h
  · exact hsep f c (hf.symm.trans h)
  · exact hsep f d (hf.symm.trans h)

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! All disk/exterior and different-disk segment interactions are genuinely disjoint. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry

theorem round_chord_exterior_disjoint (z a b c d : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hout : segment ℝ c d ⊆ {x | r^2 < squaredLength (x-z)}) : ¬ ClosedSegmentsMeet a b c d := by
  intro hh
  obtain ⟨x,hx,hy⟩ := (closedSegmentsMeet_iff_nonempty_inter _ _ _ _).mp hh
  have hle := round_chord_subset_closed_disk z a b r ha hb hx
  have hlt : r^2 < squaredLength (x-z) := hout hy
  change squaredLength (x-z) ≤ r^2 at hle
  exact not_lt_of_ge hle hlt

namespace TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem different_vertex_chords_disjoint (j k : Vertex) (hjk : j ≠ k)
    (a b : IncidentEdges graph j) (c d : IncidentEdges graph k) (ε : ℝ)
    (hc : |V.spokeScale k c*ε|≤1) (hd : |V.spokeScale k d*ε|≤1) :
    ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε) := by
  apply not_closedSegmentsMeet_of_disjoint
  exact (V.disks_disjoint j k hjk).mono
    (round_chord_subset_closed_disk _ _ _ _ (V.spokePort_circle j a) (V.spokePort_circle j b))
    (round_chord_subset_closed_disk _ _ _ _ (C.shiftedPort_circle k c ε hc) (C.shiftedPort_circle k d ε hd))

theorem chord_connector_disjoint_all_passages (j : Vertex) (a b f : IncidentEdges graph j)
    (ε : ℝ) (hne : ε ≠ 0) (hsmall : |V.spokeScale j f*ε|<1)
    (ha : V.spokePort j a ≠ C.shiftedPort j f ε) (hb : V.spokePort j b ≠ C.shiftedPort j f ε) :
    ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j f ε) (C.tangentPort j f ε) := by
  rintro ⟨s,hs,t,ht,he⟩
  have hx : segmentPoint (V.spokePort j a) (V.spokePort j b) s ∈ segment ℝ (V.spokePort j a) (V.spokePort j b) := by
    rw [← Path.range_segment]
    exact ⟨⟨s,hs⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]⟩
  have hinside := round_chord_subset_closed_disk (D.vertex j) _ _ V.radius
    (V.spokePort_circle j a) (V.spokePort_circle j b) hx
  by_cases htp : 0<t
  · have hout := C.connector_strictly_outside j f ε hsmall hne t htp
    rw [← he] at hout
    exact not_lt_of_ge hinside hout
  · have ht0 : t=0 := by linarith [ht.1]
    rw [ht0,segmentPoint_zero] at he
    have hboundary : squaredLength (segmentPoint (V.spokePort j a) (V.spokePort j b) s-D.vertex j)=V.radius^2 := by
      rw [he]
      exact C.shiftedPort_circle j f ε hsmall.le
    rcases round_chord_boundary_endpoints (D.vertex j) _ _ _ V.radius
      (V.spokePort_circle j a) (V.spokePort_circle j b) hx hboundary with h | h
    · exact ha (h.symm.trans he)
    · exact hb (h.symm.trans he)

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! One radius verifies every track, connector and chord interaction needed for actual closed-walk assembly. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_cross_type_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ →
      (∀ j (f : IncidentEdges graph j) e (i : Fin (V.pieces e)),
        ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
          (C.shiftedPort j f ε) (C.tangentPort j f ε)) ∧
      (∀ j (c d : IncidentEdges graph j) e (i : Fin (V.pieces e)),
        ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
          (C.shiftedPort j c ε) (C.shiftedPort j d ε)) ∧
      (∀ j (a b : IncidentEdges graph j) e (i : Fin (V.pieces e)),
        ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b)
          (shiftedTrack (V.vertices e) (V.pieces e) ε i.val)
          (shiftedTrack (V.vertices e) (V.pieces e) ε (i.val+1))) ∧
      (∀ j k (a b : IncidentEdges graph j) (f : IncidentEdges graph k),
        ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b)
          (C.shiftedPort k f ε) (C.tangentPort k f ε)) ∧
      (∀ j k (a b : IncidentEdges graph j) (c d : IncidentEdges graph k), a ≠ b → c ≠ d →
        SegmentPairTransverse (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε)) ∧
      (∀ j k, j ≠ k → ∀ (a b : IncidentEdges graph j) (c d : IncidentEdges graph k),
        ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε)) := by
  obtain ⟨δ₀,hδ₀,htracks⟩ := V.exists_all_vertex_disk_radius
  obtain ⟨δ₁,hδ₁,hconnectors⟩ := C.exists_all_connector_track_radius hnorm
  obtain ⟨δ₂,hδ₂,hother⟩ := C.exists_connector_other_disks_radius
  obtain ⟨δ₃,hδ₃,hseparate⟩ := C.exists_uniform_endpoint_radius
  obtain ⟨δ₄,hδ₄,hscale⟩ := C.exists_uniform_scale_radius
  let δ := min δ₀ (min δ₁ (min δ₂ (min δ₃ δ₄)))
  have hδ : 0<δ := lt_min hδ₀ (lt_min hδ₁ (lt_min hδ₂ (lt_min hδ₃ hδ₄)))
  have hb₀ : δ≤δ₀ := min_le_left _ _
  have hb₁ : δ≤δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hb₂ : δ≤δ₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb₃ : δ≤δ₃ := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hb₄ : δ≤δ₄ := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall
  have hs := hscale ε (hsmall.trans_le hb₄)
  have hsep := hseparate ε hε (hsmall.trans_le hb₃)
  refine ⟨hconnectors ε hε (hsmall.trans_le hb₁),?_,?_,?_,?_,?_⟩
  · intro j c d e i
    exact C.track_shifted_chord_disjoint j c d ε (hs j c).le (hs j d).le (hsep j).1 e i
  · intro j a b e i
    exact round_chord_exterior_disjoint (D.vertex j) _ _ _ _ V.radius
      (V.spokePort_circle j a) (V.spokePort_circle j b) (htracks ε hε (hsmall.trans_le hb₀) j e i)
  · intro j k a b f
    by_cases hjk : j=k
    · subst k
      exact C.chord_connector_disjoint_all_passages j a b f ε hε (hs j f) ((hsep j).1 a f) ((hsep j).1 b f)
    · exact round_chord_exterior_disjoint (D.vertex j) _ _ _ _ V.radius
        (V.spokePort_circle j a) (V.spokePort_circle j b)
        (hother ε (hsmall.trans_le hb₂) k j (Ne.symm hjk) f)
  · intro j k a b c d hab hcd
    by_cases hjk : j=k
    · subst k
      exact C.shifted_chords_transverse j a b c d ε (fun e => (hs j e).le) (hsep j).1 (hsep j).2 hab hcd
    · exact segmentPairTransverse_of_not_meet _ _ _ _
        (C.different_vertex_chords_disjoint j k hjk a b c d ε (hs k c).le (hs k d).le)
  · intro j k hjk a b c d
    exact C.different_vertex_chords_disjoint j k hjk a b c d ε (hs k c).le (hs k d).le

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

end OAI
