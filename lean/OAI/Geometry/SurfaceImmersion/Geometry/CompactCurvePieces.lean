import OAI.Geometry.SurfaceImmersion.Whitney.FiniteCurveArcCover
import OAI.Geometry.SurfaceImmersion.Whitney.FiniteArcPieces

namespace OAI

/-! A compact curve with the proved line/half-line charts admits a finite
partition into open connected pieces and finitely many vertices. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]

theorem compact_curve_pieces (D : Set X) (hD : D.Finite)
    (hchart : ∀ x : X,
      (∃ c : OpenPartialHomeomorph X ℝ, x ∈ c.source) ∨
      (∃ c : OpenPartialHomeomorph X (Ici (0:ℝ)), x ∈ c.source ∧ c x = ⟨0,by simp⟩)) :
    ∃ (V : Set X) (P : Finset (Set X)), V.Finite ∧ D ⊆ V ∧
      (∀ E ∈ P, IsOpen E ∧ IsConnected E ∧ Disjoint E V ∧ closure E \ E ⊆ V) ∧
      (∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F) ∧ Vᶜ = ⋃ E ∈ P, E ∧ (∀ E ∈ P, Nonempty (CurveEdgeWitness V E)) := by
  classical
  obtain ⟨A,W,s,hW,hs⟩ := finite_curve_arc_cover hchart
  let A' : s → CompactCurveArc X := fun i => A i.val
  let l : s → X := fun i => (A' i).map ⟨(A' i).left,le_rfl,(A' i).ordered.le⟩
  let r : s → X := fun i => (A' i).map ⟨(A' i).right,(A' i).ordered.le,le_rfl⟩
  let V := D ∪ (range l ∪ range r)
  have hV : V.Finite := hD.union ((finite_range l).union (finite_range r))
  have hcover : (univ : Set X) ⊆ ⋃ i : s, range (A' i).map := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,(hW i).2.2 hxi⟩
  obtain ⟨P,hP,hd,hc,hE⟩ := finite_arc_pieces A' V hV
    (fun i => Or.inr (Or.inl (mem_range_self i)))
    (fun i => Or.inr (Or.inr (mem_range_self i))) hcover
  exact ⟨V,P,hV,subset_union_left,hP,hd,hc,hE⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
