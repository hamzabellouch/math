import OAI.Combinatorics.Crossing.DrawingExteriorReplacement
import OAI.Combinatorics.Crossing.DiskFillingContainment

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

structure PolygonalExterior (C : DrawingPassages D) where
  chain : ∀ i : C.ArcIndex, PolygonalChain Set.univ (C.arcStart i) (C.arcEnd i)
  injective : ∀ i, Function.Injective (chain i).path
  outside : ∀ i t, t ∈ Set.Ioo (0 : unitInterval) 1 →
    (chain i).path t ∈ outsideDisks (fun x : DrawingMark D => x.val) C.radius
  disjoint : ∀ i j, i ≠ j → Disjoint (Set.range (chain i).path) (Set.range (chain j).path)

theorem nonempty_polygonalExterior (C : DrawingPassages D) : Nonempty (PolygonalExterior C) := by
  classical
  let : Fintype (DrawingMark D) := (drawingMarks_finite D).fintype
  obtain ⟨U,P,hU,hP,hout,hdisjoint⟩ := finite_exterior_arc_replacements
    (fun x : DrawingMark D => x.val) C.radius C.radius_pos C.disks_disjoint
    C.arcStartMark C.arcEndMark C.arcStart C.arcEnd C.arc_endpoints_ne
    C.arc_start_on_circle C.arc_end_on_circle C.arc C.arcs_pairwise_disjoint C.arc_interior_outside
  exact ⟨{
    chain := fun i => (P i).widen (Set.subset_univ _)
    injective := hP
    outside := hout
    disjoint := hdisjoint }⟩

namespace PolygonalExterior
variable {C : DrawingPassages D}

theorem outside_open_disks (E : PolygonalExterior C) (i : C.ArcIndex) (t : unitInterval)
    (x : DrawingMark D) : C.radius^2 ≤ squaredLength ((E.chain i).path t-x.val) := by
  by_cases ht0 : t=0
  · subst t
    rw [(E.chain i).path.source]
    exact C.portPoint_outside_open_disks (i,false) x
  by_cases ht1 : t=1
  · subst t
    rw [(E.chain i).path.target]
    exact C.portPoint_outside_open_disks (i,true) x
  exact (E.outside i t ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩ x).le

theorem avoids_new_vertices (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : C.ArcIndex) (t : unitInterval) (j : BipartiteVertex m n) : (E.chain i).path t ≠ v j := by
  intro he
  have h := E.outside_open_disks i t (C.vertexMark j)
  rw [he] at h
  exact (hv j).not_ge h

theorem parameter_endpoint_of_mem_disk (E : PolygonalExterior C) (i : C.ArcIndex)
    (t : unitInterval) (x : DrawingMark D)
    (ht : (E.chain i).path t ∈ closedRoundDisk x.val C.radius) : t=0 ∨ t=1 := by
  by_cases h0 : t=0
  · exact Or.inl h0
  by_cases h1 : t=1
  · exact Or.inr h1
  have h := E.outside i t ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm h0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) h1⟩ x
  exact False.elim (h.not_ge ht)

end PolygonalExterior
end Zarankiewicz

end

end OAI
