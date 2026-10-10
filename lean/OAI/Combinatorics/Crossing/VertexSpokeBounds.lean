import OAI.Combinatorics.Crossing.VertexTraceDisks

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_small_squared_radius {ι : Type*} [Fintype ι] (ρ : ℝ) (hρ : 0 < ρ)
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ i, r^2 < L i := by
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ (fun i => min 1 (L i))
    (fun i _ => lt_min (by norm_num) (hL i))
  refine ⟨min ρ δ,lt_min hρ hδ,min_le_left _ _,?_⟩
  intro i
  have hh := (min_le_right ρ δ).trans_lt (hbound i (Finset.mem_univ _))
  have h1 := hh.trans_le (min_le_left 1 (L i))
  have hlen := hh.trans_le (min_le_right 1 (L i))
  have hpos := lt_min hρ hδ
  have hm := mul_pos hpos (sub_pos.mpr h1)
  nlinarith

theorem exists_vertex_spoke_bound {m n : ℕ} (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ e,
      r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
  let L : BipartiteEdge m n → ℝ := fun e =>
    min (squaredLength ((P e).vertices 1-(P e).vertices 0))
      (squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
  have hL (e : BipartiteEdge m n) : 0 < L e := by
    have hp := drawing_chain_pieces_pos D e (P e)
    have hlast := (P e).minimum_piece_ne_zero (hmin e) ((P e).pieces-1) (by omega)
    rw [show (P e).pieces-1+1=(P e).pieces by omega] at hlast
    exact lt_min (squaredLength_pos _ ((P e).minimum_piece_ne_zero (hmin e) 0 hp))
      (squaredLength_pos _ hlast)
  obtain ⟨r,hr,hrρ,hbound⟩ := exists_small_squared_radius ρ hρ L hL
  exact ⟨r,hr,hrρ,fun e => ⟨(hbound e).trans_le (min_le_left _ _),
    (hbound e).trans_le (min_le_right _ _)⟩⟩

end Zarankiewicz

end

end OAI
