import OAI.Combinatorics.CompleteCrossing.Tracks
import OAI.Combinatorics.Crossing.MovingDiskClearance
import OAI.Combinatorics.Crossing.NormalOffsetExterior

namespace OAI

/-! Radial track displacements and connector clearance from other disks and tracks. -/

section

/-! Endpoint radial directions have the correct sign in the fixed left-to-right edge orientation. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry

theorem dot2_scaled_self (v : Plane) (a b : ℝ) : dot2 (a • v) (b • v)=a*b*squaredLength v := by
  dsimp [dot2,squaredLength]
  ring

namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem start_radial_dot_pos (e : Edge) :
    0 < dot2 (V.startPort e-D.vertex ((graph.src e))) (trackDirection (V.vertices e) 0) := by
  have hp := V.pieces_pos e
  have hα := (radialPort_parameter_half ((V.chain e).vertices 0) ((V.chain e).vertices 1)
    V.radius V.radius_pos (V.short e).1).1
  have hβ := (V.chain e).truncatedScale_pos V.radius V.radius_pos (V.short e).1 (V.short e).2 0
  have he : V.startPort e-D.vertex ((graph.src e))=
      (V.chain e).startFraction V.radius • trackDirection (V.chain e).vertices 0 := by
    have hh := radialPort_sub ((V.chain e).vertices 0) ((V.chain e).vertices 1) V.radius
    change (V.chain e).startPort V.radius-(V.chain e).vertices 0=
      (V.chain e).startFraction V.radius • trackDirection (V.chain e).vertices 0 at hh
    simpa only [startPort,(V.chain e).first] using hh
  rw [he]
  change 0 < dot2 _ (trackDirection ((V.chain e).truncatedVertices V.radius) 0)
  rw [(V.chain e).truncated_direction V.radius 0 hp,dot2_scaled_self]
  exact mul_pos (mul_pos hα hβ)
    (squaredLength_pos _ ((V.chain e).minimum_piece_ne_zero (V.minimal e) 0 hp))

theorem end_radial_dot_neg (e : Edge) :
    dot2 (V.endPort e-D.vertex ((graph.dst e)))
      (trackDirection (V.vertices e) (V.pieces e-1)) < 0 := by
  have hp := V.pieces_pos e
  have hp' : 0 < (V.chain e).pieces := hp
  have hi : V.pieces e-1 < V.pieces e := by omega
  have hα := (radialPort_parameter_half ((V.chain e).vertices ((V.chain e).pieces-1))
    ((V.chain e).vertices (V.chain e).pieces) V.radius V.radius_pos (V.short e).2).1
  have hβ := (V.chain e).truncatedScale_pos V.radius V.radius_pos (V.short e).1 (V.short e).2 (V.pieces e-1)
  have he : V.endPort e-D.vertex ((graph.dst e))=
      (-(V.chain e).endFraction V.radius) • trackDirection (V.chain e).vertices (V.pieces e-1) := by
    have hh : (V.chain e).endPort V.radius-(V.chain e).vertices (V.chain e).pieces=
        (-(V.chain e).endFraction V.radius) • trackDirection (V.chain e).vertices (V.pieces e-1) := by
      rw [(V.chain e).endPort_eq_fraction]
      simp only [trackDirection,pieces,show (V.chain e).pieces-1+1=(V.chain e).pieces by omega,neg_smul]
      abel
    simpa only [endPort,(V.chain e).last] using hh
  rw [he]
  change dot2 _ (trackDirection ((V.chain e).truncatedVertices V.radius) (V.pieces e-1)) < 0
  rw [(V.chain e).truncated_direction V.radius _ hi,dot2_scaled_self]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hα) hβ)
    (squaredLength_pos _ ((V.chain e).minimum_piece_ne_zero (V.minimal e) _ hi))

theorem bend_ne_zero (e : Edge) (i : ℕ) (hi0 : 0 < i) (hin : i < V.pieces e) :
    det2 (trackDirection (V.vertices e) (i-1)) (trackDirection (V.vertices e) i) ≠ 0 := by
  exact (V.chain e).truncated_bend_ne_zero (V.minimal e) V.radius V.radius_pos
    (V.short e).1 (V.short e).2 i hi0 hin

theorem exists_forward_radius (e : Edge) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ i : Fin (V.pieces e),
      ∃ ℓ : ℝ, 0<ℓ ∧ shiftedTrack (V.vertices e) (V.pieces e) ε (i.val+1)-
        shiftedTrack (V.vertices e) (V.pieces e) ε i.val=ℓ • trackDirection (V.vertices e) i.val :=
  exists_forward_shiftedTrack_radius (V.vertices e) (V.pieces e) (V.direction_ne_zero e) (V.bend_ne_zero e)

end VertexTruncation
end Paper170Geometry

end
end

section

/-! The actual first and last shifted segments remain outside their incident vertex disks. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem shifted_first_piece_exterior (e : Edge) (ε ℓ : ℝ)
    (hε : ε ≠ 0) (hℓ : 0<ℓ)
    (hdir : shiftedTrack (V.vertices e) (V.pieces e) ε 1-
      shiftedTrack (V.vertices e) (V.pieces e) ε 0=ℓ • trackDirection (V.vertices e) 0) :
    segment ℝ (shiftedTrack (V.vertices e) (V.pieces e) ε 0)
      (shiftedTrack (V.vertices e) (V.pieces e) ε 1) ⊆
      {x | V.radius^2 < squaredLength (x-D.vertex ((graph.src e)))} := by
  have hstart : shiftedTrack (V.vertices e) (V.pieces e) ε 0=
      V.startPort e+ε • normalShift (trackDirection (V.vertices e) 0) := by
    simp [shiftedTrack,trackOffset,V.vertices_first]
  have hc : squaredLength (V.startPort e-D.vertex ((graph.src e)))=V.radius^2 := by
    simpa only [V.spokePort_left] using V.spokePort_circle ((graph.src e)) (V.leftIncident e)
  have hp : det2 (trackDirection (V.vertices e) 0) (V.startPort e-D.vertex ((graph.src e)))=0 := by
    simpa [spokeDirection,spokeIndex,leftIncident,spokePort,drawingSpokePort,startPort] using
      V.spokeDirection_parallel ((graph.src e)) (V.leftIncident e)
  rw [hstart] at hdir ⊢
  exact normal_offset_segment_exterior _ _ _ _ _ ε ℓ (V.direction_ne_zero e 0 (V.pieces_pos e))
    hc hp (mul_nonneg hℓ.le (V.start_radial_dot_pos e).le) hε hdir

theorem shifted_last_piece_exterior (e : Edge) (ε ℓ : ℝ)
    (hε : ε ≠ 0) (hℓ : 0<ℓ)
    (hdir : shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e)-
      shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e-1)=
        ℓ • trackDirection (V.vertices e) (V.pieces e-1)) :
    segment ℝ (shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e-1))
      (shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e)) ⊆
      {x | V.radius^2 < squaredLength (x-D.vertex ((graph.dst e)))} := by
  have hn : V.pieces e ≠ 0 := ne_of_gt (V.pieces_pos e)
  have hi : V.pieces e-1 < V.pieces e := by have hh := V.pieces_pos e; omega
  have hend : shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e)=
      V.endPort e+ε • normalShift (trackDirection (V.vertices e) (V.pieces e-1)) := by
    simp [shiftedTrack,trackOffset,hn,V.vertices_last]
  have hc : squaredLength (V.endPort e-D.vertex ((graph.dst e)))=V.radius^2 := by
    simpa only [V.spokePort_right] using V.spokePort_circle ((graph.dst e)) (V.rightIncident e)
  have hp : det2 (trackDirection (V.vertices e) (V.pieces e-1)) (V.endPort e-D.vertex ((graph.dst e)))=0 := by
    simpa [spokeDirection,spokeIndex,rightIncident,spokePort,drawingSpokePort,endPort,(graph.loopless e).symm] using
      V.spokeDirection_parallel ((graph.dst e)) (V.rightIncident e)
  have hrev : shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e-1)-
      (V.endPort e+ε • normalShift (trackDirection (V.vertices e) (V.pieces e-1)))=
        (-ℓ) • trackDirection (V.vertices e) (V.pieces e-1) := by
    rw [neg_smul,← hdir,hend]
    abel
  rw [segment_symm,hend]
  exact normal_offset_segment_exterior _ _ _ _ _ ε (-ℓ) (V.direction_ne_zero e _ hi)
    hc hp (mul_nonneg_of_nonpos_of_nonpos (by linarith) (V.end_radial_dot_neg e).le) hε hrev

end Paper170Geometry.VertexTruncation

end
end

section

/-! Actual connectors stay on the displaced supporting line and avoid their own original spoke piece. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry

theorem det2_segmentPoint_sub (d p a b : Plane) (t : ℝ) :
    det2 d (segmentPoint a b t-p)=(1-t)*det2 d (a-p)+t*det2 d (b-p) := by
  dsimp [det2,segmentPoint]
  ring

theorem segment_line_level_zero (a b p : Plane) (hp : p=a ∨ p=b) (t : ℝ) :
    det2 (b-a) (segmentPoint a b t-p)=0 := by
  rcases hp with rfl | rfl <;> dsimp [det2,segmentPoint] <;> ring

namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem spokePort_is_piece_endpoint (j : Vertex) (e : IncidentEdges graph j) :
    V.spokePort j e=V.vertices e.val (V.spokeIndex j e) ∨
      V.spokePort j e=V.vertices e.val (V.spokeIndex j e+1) := by
  unfold spokePort drawingSpokePort spokeIndex
  split_ifs
  · exact Or.inl (V.vertices_first e.val).symm
  · right
    have hp := V.pieces_pos e.val
    rw [show V.pieces e.val-1+1=V.pieces e.val by omega]
    exact (V.vertices_last e.val).symm

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem continuous_tangentPort (j : Vertex) (e : IncidentEdges graph j) :
    Continuous (C.tangentPort j e) := by
  change Continuous (fun ε : ℝ => V.spokePort j e+ε • normalShift (V.spokeDirection j e))
  fun_prop

theorem tangentPort_zero (j : Vertex) (e : IncidentEdges graph j) :
    C.tangentPort j e 0=V.spokePort j e := by simp [tangentPort]

theorem tangentPort_level (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ) :
    det2 (V.spokeDirection j e) (C.tangentPort j e ε-V.spokePort j e)=ε := by
  simp only [tangentPort,add_sub_cancel_left,det2_smul_right,
    det2_normalShift _ (V.spokeDirection_ne_zero j e),mul_one]

theorem connector_level (j : Vertex) (e : IncidentEdges graph j) (ε t : ℝ) :
    det2 (V.spokeDirection j e)
      (segmentPoint (C.shiftedPort j e ε) (C.tangentPort j e ε) t-V.spokePort j e)=ε := by
  rw [det2_segmentPoint_sub,C.shiftedPort_level,C.tangentPort_level]
  ring

theorem connector_avoids_incident_piece (j : Vertex) (e : IncidentEdges graph j)
    (ε : ℝ) (hε : ε ≠ 0) :
    ¬ ClosedSegmentsMeet (V.vertices e.val (V.spokeIndex j e))
      (V.vertices e.val (V.spokeIndex j e+1)) (C.shiftedPort j e ε) (C.tangentPort j e ε) := by
  rintro ⟨s,hs,t,ht,he⟩
  have hzero := segment_line_level_zero (V.vertices e.val (V.spokeIndex j e))
    (V.vertices e.val (V.spokeIndex j e+1)) (V.spokePort j e) (V.spokePort_is_piece_endpoint j e) s
  change det2 (V.spokeDirection j e)
    (segmentPoint (V.vertices e.val (V.spokeIndex j e)) (V.vertices e.val (V.spokeIndex j e+1)) s-V.spokePort j e)=0 at hzero
  rw [he,C.connector_level] at hzero
  exact hε hzero

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! One genuine radius keeps every shifted exterior edge track outside every vertex disk. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem exists_nonincident_shift_radius [Fintype Vertex] [Fintype Edge] :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ j e (i : Fin (V.pieces e)),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=V.pieces e)) →
      segment ℝ (shiftedTrack (V.vertices e) (V.pieces e) ε i.val)
        (shiftedTrack (V.vertices e) (V.pieces e) ε (i.val+1)) ⊆
          {x | V.radius^2 < squaredLength (x-D.vertex j)} := by
  classical
  let Bad := Σ j : Vertex, Σ e : Edge,
    {i : Fin (V.pieces e) // ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=V.pieces e))}
  have hdis (b : Bad) : Disjoint (closedRoundDisk (D.vertex b.1) V.radius)
      (segment ℝ (V.vertices b.2.1 b.2.2.val.val) (V.vertices b.2.1 (b.2.2.val.val+1))) := by
    exact (V.piece_clearance b.1 b.2.1 b.2.2.val b.2.2.property).mono_right
      ((V.chain b.2.1).truncated_piece_subset V.radius V.radius_pos
        (V.weak_short b.2.1).1 (V.weak_short b.2.1).2 _ b.2.2.val.isLt)
  have hex (b : Bad) := exists_shifted_segment_disk_radius
    (V.vertices b.2.1 b.2.2.val.val) (V.vertices b.2.1 (b.2.2.val.val+1))
    (trackOffset (V.vertices b.2.1) (V.pieces b.2.1) b.2.2.val.val)
    (trackOffset (V.vertices b.2.1) (V.pieces b.2.1) (b.2.2.val.val+1))
    (D.vertex b.1) V.radius (hdis b)
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun b _ => hpos b)
  refine ⟨δ,hδ,?_⟩
  intro ε hε j e i hi
  exact hprop ⟨j,e,⟨i,hi⟩⟩ ε (hε.trans (hbound ⟨j,e,⟨i,hi⟩⟩ (Finset.mem_univ _)))

theorem exists_all_vertex_disk_radius [Fintype Vertex] [Fintype Edge] :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j e (i : Fin (V.pieces e)),
      segment ℝ (shiftedTrack (V.vertices e) (V.pieces e) ε i.val)
        (shiftedTrack (V.vertices e) (V.pieces e) ε (i.val+1)) ⊆
          {x | V.radius^2 < squaredLength (x-D.vertex j)} := by
  classical
  obtain ⟨δ₀,hδ₀,hclear⟩ := V.exists_nonincident_shift_radius
  choose radius hpos hforward using V.exists_forward_radius
  obtain ⟨δ₁,hδ₁,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun e _ => hpos e)
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro ε hε hsmall j e i
  obtain ⟨ℓ,hℓ,hdir⟩ := hforward e ε
    (hsmall.trans_le (min_le_right _ _ ) |>.trans (hbound e (Finset.mem_univ _))) i
  by_cases hleft : j=(graph.src e) ∧ i.val=0
  · rcases hleft with ⟨rfl,hi⟩
    simpa only [hi,zero_add] using V.shifted_first_piece_exterior e ε ℓ hε hℓ (by simpa only [hi,zero_add] using hdir)
  · by_cases hright : j=(graph.dst e) ∧ i.val+1=V.pieces e
    · rcases hright with ⟨rfl,hi⟩
      have hi' : i.val=V.pieces e-1 := by omega
      have hn : V.pieces e-1+1=V.pieces e := by omega
      simpa only [hi',hn] using V.shifted_last_piece_exterior e ε ℓ hε hℓ (by simpa only [hi',hn] using hdir)
    · exact hclear ε (hsmall.trans_le (min_le_left _ _)) j e i (not_or.mpr ⟨hleft,hright⟩)

end Paper170Geometry.VertexTruncation

end
end

section

/-! Every shrinking circle connector stays outside all other vertex disks at one common radius. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
open scoped Topology
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem exists_connector_other_disks_radius [Fintype Vertex] [Fintype Edge] :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ j k, j ≠ k → ∀ f : IncidentEdges graph j,
      segment ℝ (C.shiftedPort j f ε) (C.tangentPort j f ε) ⊆
        {x | V.radius^2 < squaredLength (x-D.vertex k)} := by
  classical
  let Pair := Σ j : Vertex, Σ k : {k : Vertex // j ≠ k}, IncidentEdges graph j
  have hstart (b : Pair) : segment ℝ (C.shiftedPort b.1 b.2.2 0) (C.tangentPort b.1 b.2.2 0) ⊆
      {x | V.radius^2 < squaredLength (x-D.vertex b.2.1.val)} := by
    rw [C.shiftedPort_zero,C.tangentPort_zero,segment_same]
    intro x hx
    have he : x=V.spokePort b.1 b.2.2 := hx
    subst x
    change V.radius^2 < squaredLength (V.spokePort b.1 b.2.2-D.vertex b.2.1.val)
    by_contra hh
    have hj : V.spokePort b.1 b.2.2 ∈ closedRoundDisk (D.vertex b.1) V.radius := by
      change squaredLength (V.spokePort b.1 b.2.2-D.vertex b.1) ≤ V.radius^2
      rw [V.spokePort_circle]
    have hk : V.spokePort b.1 b.2.2 ∈ closedRoundDisk (D.vertex b.2.1.val) V.radius := not_lt.mp hh
    exact Set.disjoint_left.mp (V.disks_disjoint b.1 b.2.1.val b.2.1.property) hj hk
  have hevent (b : Pair) := eventually_moving_segment_outside_disk
    (C.shiftedPort b.1 b.2.2) (C.tangentPort b.1 b.2.2)
    (C.continuous_shiftedPort b.1 b.2.2) (C.continuous_tangentPort b.1 b.2.2)
    (D.vertex b.2.1.val) V.radius (hstart b)
  have hex (b : Pair) := Metric.eventually_nhds_iff.mp (hevent b)
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun b _ => hpos b)
  refine ⟨δ,hδ,?_⟩
  intro ε hε j k hjk f
  exact hprop ⟨j,⟨k,hjk⟩,f⟩ (by simpa [Real.dist_eq] using hε.trans (hbound ⟨j,⟨k,hjk⟩,f⟩ (Finset.mem_univ _)))

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! One two-sided physical radius excludes every connector/track meeting, including shared edges. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
open scoped Topology
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_nonincident_connector_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ j (f : IncidentEdges graph j) e (i : Fin (V.pieces e)),
      ¬ (e=f.val ∧ i.val=V.spokeIndex j f) →
      ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
        (C.shiftedPort j f ε) (C.tangentPort j f ε) := by
  classical
  let Bad := Σ j : Vertex, Σ f : IncidentEdges graph j, Σ e : Edge,
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

theorem exists_all_connector_track_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j (f : IncidentEdges graph j) e (i : Fin (V.pieces e)),
      ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
        (C.shiftedPort j f ε) (C.tangentPort j f ε) := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_nonincident_connector_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall j f e i
  by_cases hi : e=f.val ∧ i.val=V.spokeIndex j f
  · rcases hi with ⟨rfl,hi⟩
    simpa only [hi] using C.connector_avoids_incident_piece j f ε hε
  · exact hh ε hsmall j f e i hi

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

end OAI
