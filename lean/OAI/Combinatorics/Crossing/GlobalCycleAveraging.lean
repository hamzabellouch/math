import OAI.Combinatorics.Crossing.VertexPassagePairing

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem closed_cycle_averaged_sum (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (d f : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (N K : ℕ) (hN : d N=d 0) (hK : f K=f 0)
    (hdi : ∀ i, i < N → bipartiteDartEdge (d (i+1)) ≠ bipartiteDartEdge (d i))
    (hfj : ∀ j, j < K → bipartiteDartEdge (f (j+1)) ≠ bipartiteDartEdge (f j)) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
      (bipartiteDartSign (d i)*bipartiteDartSign (f j)*
        V.signedIntersection (bipartiteDartEdge (d i)) (bipartiteDartEdge (f j))+
          C.passagePairing d f hd hf i j)=0 := by
  obtain ⟨δ₀,hδ₀,hglobal⟩ := C.exists_closed_cycle_intersection_radius hnorm hstraight htrans
  obtain ⟨δ₁,hδ₁,hlocal⟩ := C.exists_passage_pairing_radius hnorm
  let t := min δ₀ δ₁/2
  have ht : 0 < t := half_pos (lt_min hδ₀ hδ₁)
  have htmin : t < min δ₀ δ₁ := half_lt_self (lt_min hδ₀ hδ₁)
  have ht₀ : t < δ₀ := htmin.trans_le (min_le_left _ _)
  have ht₁ : t < δ₁ := htmin.trans_le (min_le_right _ _)
  have hzplus := hglobal t (ne_of_gt ht) (by simpa only [abs_of_pos ht] using ht₀) d f hd hf N K hN hK hdi hfj
  have hzminus := hglobal (-t) (neg_ne_zero.mpr (ne_of_gt ht))
    (by simpa only [abs_neg,abs_of_pos ht] using ht₀) d f hd hf N K hN hK hdi hfj
  let E : ℕ → ℕ → ℝ := fun i j => bipartiteDartSign (d i)*bipartiteDartSign (f j)*
    V.signedIntersection (bipartiteDartEdge (d i)) (bipartiteDartEdge (f j))
  calc
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        ((E i j+C.passageIntersection d f hd hf i j t)+
          (E i j+C.passageIntersection d f hd hf i j (-t)))/2 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [← hlocal t ht ht₁ d f hd hf i j (hdi i (Finset.mem_range.mp hi)) (hfj j (Finset.mem_range.mp hj))]
      dsimp only [E]
      ring
    _ = ((∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, (E i j+C.passageIntersection d f hd hf i j t))+
        (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, (E i j+C.passageIntersection d f hd hf i j (-t))))/2 := by
      simp only [div_eq_mul_inv,Finset.sum_add_distrib,Finset.sum_mul,add_mul]
    _ = 0 := by rw [hzplus,hzminus]; norm_num

theorem graph_cycles_averaged_sum (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    {u v : BipartiteVertex m n} (p : (completeBipartite m n).Walk u u)
    (q : (completeBipartite m n).Walk v v) (hp : p.IsCycle) (hq : q.IsCycle) :
    let dp := cyclicWalkDart p (by have := hp.three_le_length; omega)
    let dq := cyclicWalkDart q (by have := hq.three_le_length; omega)
    let sp := cyclicWalkDart_seam p (by have := hp.three_le_length; omega)
    let sq := cyclicWalkDart_seam q (by have := hq.three_le_length; omega)
    ∑ i ∈ Finset.range p.length, ∑ j ∈ Finset.range q.length,
      (bipartiteDartSign (dp i)*bipartiteDartSign (dq j)*
        V.signedIntersection (bipartiteDartEdge (dp i)) (bipartiteDartEdge (dq j))+
          C.passagePairing dp dq sp sq i j)=0 := by
  dsimp only
  exact C.closed_cycle_averaged_sum hnorm hstraight htrans _ _ _ _ _ _
    (cyclicWalkDart_period p _) (cyclicWalkDart_period q _)
    (fun i _ => cyclicWalkDart_next_edge_ne p hp i) (fun j _ => cyclicWalkDart_next_edge_ne q hq j)

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
