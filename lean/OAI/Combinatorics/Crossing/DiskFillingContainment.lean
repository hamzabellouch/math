import OAI.Combinatorics.Crossing.CrossingDiskIncidence
import OAI.Combinatorics.Crossing.DrawingVertexPlacement

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem round_chord_in_disk (z a b : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    squaredLength (segmentPoint a b t-z) ≤ r^2 := by
  have he : squaredLength (segmentPoint a b t-z)=
      (1-t)*squaredLength (a-z)+t*squaredLength (b-z)-t*(1-t)*squaredLength (b-a) := by
    dsimp [squaredLength,segmentPoint]
    ring
  have hnon : 0 ≤ t*(1-t)*squaredLength (b-a) := by
    apply mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
    dsimp [squaredLength]
    positivity
  rw [he,ha,hb]
  linarith

namespace DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem crossingChord_range_subset_disk (C : DrawingPassages D) (p : C.InnerIndex) :
    Set.range (C.crossingChord p) ⊆ closedRoundDisk (C.innerMark p).val C.radius := by
  rintro x ⟨t,rfl⟩
  change squaredLength ((Path.segment _ _) t-(C.innerMark p).val) ≤ C.radius^2
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact round_chord_in_disk _ _ _ _ (C.incomingPoint_on_circle p) (C.outgoingPoint_on_circle p) t.val t.property

theorem crossingChord_interior_in_disk (C : DrawingPassages D) (p : C.InnerIndex)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) :
    squaredLength (C.crossingChord p t-(C.innerMark p).val) < C.radius^2 := by
  change squaredLength ((Path.segment _ _) t-(C.innerMark p).val) < C.radius^2
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact round_chord_in_open_disk _ _ _ _ (C.incomingPoint_on_circle p) (C.outgoingPoint_on_circle p)
    (C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p p)) t.val ht

theorem crossingChords_disjoint_of_marks_ne (C : DrawingPassages D) (p q : C.InnerIndex)
    (hm : C.innerMark p ≠ C.innerMark q) :
    Disjoint (Set.range (C.crossingChord p)) (Set.range (C.crossingChord q)) :=
  (C.disks_disjoint _ _ hm).mono (C.crossingChord_range_subset_disk p) (C.crossingChord_range_subset_disk q)

theorem portPoint_outside_other_disk (C : DrawingPassages D) (p : C.Port) (x : DrawingMark D)
    (hx : C.portMark p ≠ x) : C.radius^2 < squaredLength (C.portPoint p-x.val) := by
  apply lt_of_not_ge
  intro hh
  have hp : C.portPoint p ∈ closedRoundDisk (C.portMark p).val C.radius := (C.portPoint_on_circle p).le
  exact Set.disjoint_left.mp (C.disks_disjoint _ _ hx) hp hh

theorem portPoint_outside_open_disks (C : DrawingPassages D) (p : C.Port) (x : DrawingMark D) :
    C.radius^2 ≤ squaredLength (C.portPoint p-x.val) := by
  by_cases he : C.portMark p=x
  · have hp := C.portPoint_on_circle p
    rw [he] at hp
    exact hp.ge
  · exact (C.portPoint_outside_other_disk p x he).le

theorem crossingChord_avoids_vertex_disks (C : DrawingPassages D) (p : C.InnerIndex)
    (v : BipartiteVertex m n) :
    Disjoint (Set.range (C.crossingChord p)) (closedRoundDisk (D.vertex v) C.radius) := by
  have hn : C.innerMark p ≠ C.vertexMark v := by
    intro he
    exact crossing_not_vertex D (C.innerMark p).val (C.innerMark_is_crossing p) v (congrArg Subtype.val he)
  exact (C.disks_disjoint _ _ hn).mono (C.crossingChord_range_subset_disk p) Set.Subset.rfl

end DrawingPassages
end Zarankiewicz

end

end OAI
