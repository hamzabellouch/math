import OAI.Combinatorics.Crossing.RetainedArcDisjointness
import OAI.Combinatorics.Crossing.SimultaneousExteriorArcs

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem drawing_exterior_polygonal_replacement {m n : ℕ} (D : FiniteIntersectionDrawing m n) :
    ∃ C : DrawingPassages D, ∃ U : C.ArcIndex → Set Plane,
      ∃ P : ∀ i, PolygonalChain (U i) (C.arcStart i) (C.arcEnd i),
        (∀ i, IsOpen (U i)) ∧ (∀ i, Function.Injective (P i).path) ∧
        (∀ i t, t ∈ Set.Ioo (0 : unitInterval) 1 →
          (P i).path t ∈ outsideDisks (fun x : DrawingMark D => x.val) C.radius) ∧
        (∀ i j, i ≠ j → Disjoint (Set.range (P i).path) (Set.range (P j).path)) := by
  classical
  obtain ⟨C⟩ := nonempty_drawingPassages D
  let : Fintype (DrawingMark D) := (drawingMarks_finite D).fintype
  obtain ⟨U,P,hU,hP,hout,hdisjoint⟩ := finite_exterior_arc_replacements
    (fun x : DrawingMark D => x.val) C.radius C.radius_pos C.disks_disjoint
    C.arcStartMark C.arcEndMark C.arcStart C.arcEnd C.arc_endpoints_ne
    C.arc_start_on_circle C.arc_end_on_circle C.arc C.arcs_pairwise_disjoint C.arc_interior_outside
  exact ⟨C,U,P,hU,hP,hout,hdisjoint⟩

end Zarankiewicz

end

end OAI
