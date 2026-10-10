import OAI.Combinatorics.CompleteCrossing.Polygonalization
import OAI.Combinatorics.Crossing.CrossingReconnection

namespace OAI

/-! Crossing reconnection chords and avoidance of vertices and retained arcs. -/

section

/-! The two actual disjoint chords used in an adjacent-crossing surgery disk. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : Paper170.AdmissibleDrawing graph}

def reconnectionStart (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (i : Bool) : Plane :=
  if i then C.portPoint (C.incomingPort p) else C.portPoint (C.incomingPort q)

def reconnectionEnd (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (i : Bool) : Plane :=
  if i then C.portPoint (C.outgoingPort q) else C.portPoint (C.outgoingPort p)

theorem reconnection_endpoints_ne (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (i : Bool) :
    C.reconnectionStart p q i ≠ C.reconnectionEnd p q i := by
  cases i
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort q p)
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p q)

theorem crossingChord_meeting_segmentsCrossProperly (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hpq : p ≠ q) (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p))
    (hxq : x ∈ Set.range (C.crossingChord q)) :
    SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨s,hs⟩ := hxp
  obtain ⟨t,ht⟩ := hxq
  have he : segmentPoint (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) s.val=
      segmentPoint (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) t.val := by
    simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs.trans ht.symm
  obtain ⟨hd,hsi,hti⟩ := C.crossing_chords_transverse_at_mark p q hpq hm s.val s.property t.val t.property he
  exact ⟨hd,s.val,hsi,t.val,hti,he⟩

theorem reconnection_chords_disjoint (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q))) :
    ∀ i j : Bool, i ≠ j → Disjoint
      (segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i))
      (segment ℝ (C.reconnectionStart p q j) (C.reconnectionEnd p q j)) := by
  have hh := crossing_reconnections_disjoint _ _ _ _ hcross
  intro i j hij
  cases i <;> cases j
  · exact False.elim (hij rfl)
  · exact hh
  · exact hh.symm
  · exact False.elim (hij rfl)

theorem reconnection_endpoints_on_circle (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hm : C.innerMark p=C.innerMark q) (i : Bool) :
    squaredLength (C.reconnectionStart p q i-(C.innerMark p).val)=C.radius^2 ∧
      squaredLength (C.reconnectionEnd p q i-(C.innerMark p).val)=C.radius^2 := by
  cases i
  · change squaredLength (C.portPoint (C.incomingPort q)-(C.innerMark p).val)=C.radius^2 ∧
      squaredLength (C.portPoint (C.outgoingPort p)-(C.innerMark p).val)=C.radius^2
    exact ⟨by simpa only [hm] using C.incomingPoint_on_circle q,C.outgoingPoint_on_circle p⟩
  · change squaredLength (C.portPoint (C.incomingPort p)-(C.innerMark p).val)=C.radius^2 ∧
      squaredLength (C.portPoint (C.outgoingPort q)-(C.innerMark p).val)=C.radius^2
    exact ⟨C.incomingPoint_on_circle p,by simpa only [hm] using C.outgoingPoint_on_circle q⟩

theorem reconnection_open_in_disk (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hm : C.innerMark p=C.innerMark q) (i : Bool) :
    openSegmentTrace (C.reconnectionStart p q i) (C.reconnectionEnd p q i) ⊆ C.crossingDisk p := by
  rintro x ⟨t,ht,rfl⟩
  exact round_chord_in_open_disk _ _ _ _ (C.reconnection_endpoints_on_circle p q hm i).1
    (C.reconnection_endpoints_on_circle p q hm i).2 (C.reconnection_endpoints_ne p q i) t ht

end Paper170Geometry.DrawingPassages

end
end

section

/-! The new closed chords stay in their crossing disk and avoid all placed vertices. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : Paper170.AdmissibleDrawing graph}

theorem reconnection_segment_in_disk (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hm : C.innerMark p=C.innerMark q) (i : Bool) :
    segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i) ⊆
      closedRoundDisk (C.innerMark p).val C.radius := by
  intro x hx
  rw [← Path.range_segment] at hx
  obtain ⟨t,ht⟩ := hx
  rw [← ht]
  change squaredLength ((Path.segment _ _) t-(C.innerMark p).val) ≤ C.radius^2
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact round_chord_in_disk _ _ _ _ (C.reconnection_endpoints_on_circle p q hm i).1
    (C.reconnection_endpoints_on_circle p q hm i).2 t.val t.property

theorem reconnection_segment_avoids_vertices (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hm : C.innerMark p=C.innerMark q) (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (i : Bool) (j : Vertex) :
    v j ∉ segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i) := by
  intro hx
  have hn : C.innerMark p ≠ C.vertexMark j := by
    intro he
    exact crossing_not_vertex D.toFiniteIntersectionDrawing (C.innerMark p).val (C.innerMark_is_crossing p) j (congrArg Subtype.val he)
  exact Set.disjoint_left.mp (C.disks_disjoint _ _ hn)
    (C.reconnection_segment_in_disk p q hm i hx) (hv j).le

end Paper170Geometry.DrawingPassages

end
end

section

/-! Neither reconnection segment contains the actual point being removed. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem segment_avoids_of_affine_positive (f : Plane → ℝ) (a b x : Plane)
    (hf : ∀ t, f (segmentPoint a b t)=(1-t)*f a+t*f b)
    (ha : 0 < f a) (hb : 0 < f b) (hx : f x=0) : x ∉ segment ℝ a b := by
  intro h
  rw [← Path.range_segment] at h
  obtain ⟨t,ht⟩ := h
  have ht' : segmentPoint a b t.val=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  have hp := convex_combination_pos (f a) (f b) t.val ha hb t.property
  rw [← hf t.val,ht',hx] at hp
  exact lt_irrefl 0 hp

theorem crossing_reconnections_avoid_point (a b c d x : Plane)
    (hd : det2 (b-a) (d-c) ≠ 0) (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x=segmentPoint a b s) (hy : x=segmentPoint c d t) :
    x ∉ segment ℝ c b ∧ x ∉ segment ℝ a d := by
  let F := crossingCoordinates x (b-a) (d-c)
  have hFa : F a=(-s,0) := by
    simpa only [segmentPoint_zero,zero_sub] using crossingCoordinates_first_segment a b c d x s 0 hd hx
  have hFb : F b=(1-s,0) := by
    simpa only [segmentPoint_one] using crossingCoordinates_first_segment a b c d x s 1 hd hx
  have hFc : F c=(0,-t) := by
    simpa only [segmentPoint_zero,zero_sub] using crossingCoordinates_second_segment a b c d x t 0 hd hy
  have hFd : F d=(0,1-t) := by
    simpa only [segmentPoint_one] using crossingCoordinates_second_segment a b c d x t 1 hd hy
  have hF (u v : Plane) (r : ℝ) : F (segmentPoint u v r)=segmentPoint (F u) (F v) r :=
    crossingCoordinates_affine x (b-a) (d-c) u v r
  have hzero : F x=(0,0) := crossingCoordinates_origin x (b-a) (d-c)
  constructor
  · apply segment_avoids_of_affine_positive (fun z => (F z).1-(F z).2) c b x
    · intro r
      rw [hF]
      dsimp [segmentPoint]
      ring
    · rw [hFc]
      dsimp
      linarith [ht.1]
    · rw [hFb]
      dsimp
      linarith [hs.2]
    · rw [hzero]
      norm_num
  · apply segment_avoids_of_affine_positive (fun z => (F z).2-(F z).1) a d x
    · intro r
      rw [hF]
      dsimp [segmentPoint]
      ring
    · rw [hFa]
      dsimp
      linarith [hs.1]
    · rw [hFd]
      dsimp
      linarith [ht.2]
    · rw [hzero]
      norm_num

theorem DrawingPassages.reconnection_avoids_chord_meeting  {D : Paper170.AdmissibleDrawing graph}
    (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (hpq : p ≠ q) (x : Plane)
    (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∈ C.crossingDisk p ∧ ∀ i : Bool,
      x ∉ segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i) := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨s,hs⟩ := hxp
  obtain ⟨t,ht⟩ := hxq
  have hs' : segmentPoint (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) s.val=x := by
    simpa only [DrawingPassages.crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs
  have ht' : segmentPoint (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) t.val=x := by
    simpa only [DrawingPassages.crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  obtain ⟨hd,hsi,hti⟩ := C.crossing_chords_transverse_at_mark p q hpq hm s.val s.property t.val t.property
    (hs'.trans ht'.symm)
  constructor
  · change squaredLength (x-(C.innerMark p).val) < C.radius^2
    rw [← hs]
    exact C.crossingChord_interior_in_disk p s hsi
  · have ha := crossing_reconnections_avoid_point _ _ _ _ x hd s.val t.val hsi hti hs'.symm ht'.symm
    intro i
    cases i
    · exact ha.1
    · exact ha.2

end Paper170Geometry

end
end

end OAI
