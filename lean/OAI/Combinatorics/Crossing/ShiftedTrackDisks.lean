import OAI.Combinatorics.Crossing.ShiftedRadialPieces
import OAI.Combinatorics.Crossing.MovingDiskClearance

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

theorem exists_nonincident_shift_radius :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ j e (i : Fin (V.pieces e)),
      ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=V.pieces e)) →
      segment ℝ (shiftedTrack (V.vertices e) (V.pieces e) ε i.val)
        (shiftedTrack (V.vertices e) (V.pieces e) ε (i.val+1)) ⊆
          {x | V.radius^2 < squaredLength (x-D.vertex j)} := by
  classical
  let Bad := Σ j : BipartiteVertex m n, Σ e : BipartiteEdge m n,
    {i : Fin (V.pieces e) // ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=V.pieces e))}
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

theorem exists_all_vertex_disk_radius :
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
  by_cases hleft : j=Sum.inl e.1 ∧ i.val=0
  · rcases hleft with ⟨rfl,hi⟩
    simpa only [hi,zero_add] using V.shifted_first_piece_exterior e ε ℓ hε hℓ (by simpa only [hi,zero_add] using hdir)
  · by_cases hright : j=Sum.inr e.2 ∧ i.val+1=V.pieces e
    · rcases hright with ⟨rfl,hi⟩
      have hi' : i.val=V.pieces e-1 := by omega
      have hn : V.pieces e-1+1=V.pieces e := by omega
      simpa only [hi',hn] using V.shifted_last_piece_exterior e ε ℓ hε hℓ (by simpa only [hi',hn] using hdir)
    · exact hclear ε (hsmall.trans_le (min_le_left _ _)) j e i (not_or.mpr ⟨hleft,hright⟩)

end Zarankiewicz.VertexTruncation

end

end OAI
