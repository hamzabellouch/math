import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRetainedCrossing

namespace OAI

/-! A center-to-port interaction occurs only at an original source vertex.
Consequently source cells, under the proved no-passage condition, need only rays. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem chain_center_source (e : G.Edge) (k : ℕ) (hk : k ≤ 2*P.length e+1)
    (p : ℕ × ℕ) (hp : qmaPortChain (P.point e) (P.length e) k = qmaExpandedPoint p) :
    ∃ v, P.position v = p := by
  by_cases h0 : k = 0
  · subst k
    rw [qmaPortChain_zero,P.first] at hp
    exact ⟨G.left e,qmaExpandedPoint_injective hp⟩
  by_cases hlast : k = 2*P.length e+1
  · subst k
    rw [qmaPortChain_last,P.last] at hp
    exact ⟨G.right e,qmaExpandedPoint_injective hp⟩
  exact (qmaPortChain_inner_not_center (P.point e) (by omega) (by omega) p hp).elim

theorem graph_center_source {p y : ℕ × ℕ} (h : P.graph.Adj (qmaExpandedPoint p) y) :
    ∃ v, P.position v = p := by
  change _ ≠ _ ∧ _ at h
  rcases h.2 with ⟨e,k,hk,hl,_⟩ | ⟨e,k,hk,_,hr⟩
  · exact P.chain_center_source e k hk.le p hl
  · exact P.chain_center_source e (k+1) (by omega) p hr

theorem finished_center_source (N : ℚ) (D : ℕ) (v : Fin (P.finishedGraph N D).n)
    {p : ℕ × ℕ} (hv : P.finishedPosition N D v = qmaExpandedPoint p) :
    ∃ w, P.position w = p := by
  have h := P.toEmbedding.iterate_occupied_source N D (Or.inl ⟨v,hv⟩)
  rcases h with ⟨w,hw⟩ | ⟨e,k,hk,he⟩
  · exact ⟨w,qmaExpandedPoint_injective hw⟩
  · exact P.chain_center_source e k hk p he

theorem source_not_crossing
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v) (v : Fin G.n) :
    ¬P.IsCrossing (P.position v) := by
  rintro ⟨i,_,_,hi,_,_⟩
  exact havoid i v hi

theorem graph_center_not_crossing
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    {p y : ℕ × ℕ} (h : P.graph.Adj (qmaExpandedPoint p) y) : ¬P.IsCrossing p := by
  obtain ⟨v,rfl⟩ := P.graph_center_source h
  exact P.source_not_crossing havoid v

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
