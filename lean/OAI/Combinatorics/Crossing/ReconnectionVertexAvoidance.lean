import OAI.Combinatorics.Crossing.ReconnectionChords

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : AdmissibleDrawing m n}

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
    (hm : C.innerMark p=C.innerMark q) (v : BipartiteVertex m n → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (i : Bool) (j : BipartiteVertex m n) :
    v j ∉ segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i) := by
  intro hx
  have hn : C.innerMark p ≠ C.vertexMark j := by
    intro he
    exact crossing_not_vertex D.toFiniteIntersectionDrawing (C.innerMark p).val (C.innerMark_is_crossing p) j (congrArg Subtype.val he)
  exact Set.disjoint_left.mp (C.disks_disjoint _ _ hn)
    (C.reconnection_segment_in_disk p q hm i hx) (hv j).le

end Zarankiewicz.DrawingPassages

end

end OAI
