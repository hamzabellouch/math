import OAI.Combinatorics.Crossing.CurveDiskIsolation
import OAI.Combinatorics.Crossing.DrawingMarks

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

abbrev DrawingMark (D : FiniteIntersectionDrawing m n) := ↥(drawingMarks D)

theorem drawing_disk_isolation (D : FiniteIntersectionDrawing m n) :
    ∃ δ : BipartiteEdge m n → ℝ, ∃ r : ℝ, (∀ e, 0 < δ e) ∧ 0 < r ∧
      (∀ x y : DrawingMark D, x ≠ y →
        Disjoint (closedRoundDisk x.val r) (closedRoundDisk y.val r)) ∧
      (∀ e (x : DrawingMark D) t, D.edge e t ∈ closedRoundDisk x.val r →
        ∃ u : unitInterval, D.edge e u=x.val ∧ t ∈ parameterNeighborhood u (δ e)) ∧
      (∀ e u v, D.edge e u ∈ drawingMarks D → D.edge e v ∈ drawingMarks D → u ≠ v →
        Disjoint (closure (parameterNeighborhood u (δ e)))
          (closure (parameterNeighborhood v (δ e)))) := by
  let : Fintype (DrawingMark D) := (drawingMarks_finite D).fintype
  let : DecidableEq (DrawingMark D) := Classical.decEq _
  obtain ⟨δ,r,hδ,hr,hd,hv,hs⟩ := finite_injective_curve_disk_isolation
    (fun e => D.edge e) (fun e => (D.edge e).continuous) D.edge_injective
    (fun x : DrawingMark D => x.val) Subtype.val_injective
  refine ⟨δ,r,hδ,hr,hd,hv,?_⟩
  intro e u v hu hv huv
  exact hs e u v ⟨⟨D.edge e u,hu⟩,rfl⟩ ⟨⟨D.edge e v,hv⟩,rfl⟩ huv

end Zarankiewicz

end

end OAI
