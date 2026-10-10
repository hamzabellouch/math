import OAI.Combinatorics.Crossing.ReconnectionChords

namespace OAI

noncomputable section
namespace Zarankiewicz

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

theorem DrawingPassages.reconnection_avoids_chord_meeting {m n : ℕ} {D : AdmissibleDrawing m n}
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

end Zarankiewicz

end

end OAI
