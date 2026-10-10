import OAI.Combinatorics.Crossing.MinimumChainVertexPieces
import OAI.Combinatorics.Crossing.MarkedCurveDisks

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem exists_vertex_piece_clearance (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces) :
    ∃ r : ℝ, 0 < r ∧
      (∀ j k, j ≠ k → Disjoint (closedRoundDisk (D.vertex j) r) (closedRoundDisk (D.vertex k) r)) ∧
      (∀ j e (i : Fin (P e).pieces),
        ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces)) →
        Disjoint (closedRoundDisk (D.vertex j) r)
          (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1)))) := by
  classical
  let Bad := Σ j : BipartiteVertex m n, Σ e : BipartiteEdge m n,
    {i : Fin (P e).pieces // ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨
      (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces))}
  let K : Bad → Set Plane := fun t =>
    segment ℝ ((P t.2.1).vertices t.2.2.val.val) ((P t.2.1).vertices (t.2.2.val.val+1))
  have hK (t : Bad) : IsCompact (K t) := by
    dsimp [K]
    rw [← Path.range_segment]
    exact isCompact_range (Path.segment _ _).continuous
  have hnot (t : Bad) : D.vertex t.1 ∉ K t := by
    intro hx
    exact t.2.2.property (drawing_chain_piece_vertex D t.2.1 (P t.2.1)
      (hmin t.2.1) t.2.2.val.val t.2.2.val.isLt t.1 hx)
  obtain ⟨ρ,hρ,hclear⟩ := exists_round_disk_clearance (fun t : Bad => D.vertex t.1) K hK hnot
  obtain ⟨σ,hσ,hdis⟩ := exists_disjoint_round_disks D.vertex D.vertex_injective
  refine ⟨min ρ σ,lt_min hρ hσ,?_,?_⟩
  · intro j k hjk
    exact (hdis j k hjk).mono
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
  · intro j e i hi
    exact (hclear ⟨j,e,⟨i,hi⟩⟩).mono_left
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_left _ _))

end Zarankiewicz

end

end OAI
