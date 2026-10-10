import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRetainedCrossing
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumInnerPorts

namespace OAI

/-! Every cell touched by an actual port-graph edge lies in the positive quadrant. -/

namespace ContinuumCoulomb

def qmaPointCell (z : ℕ × ℕ) : ℕ × ℕ := (z.1/32,z.2/32)

@[simp] theorem qmaPointCell_center (p : ℕ × ℕ) : qmaPointCell (qmaExpandedPoint p) = p :=
  qmaExpandedPoint_cell p

@[simp] theorem qmaPointCell_port (p : ℕ × ℕ) (a : Fin 4) : qmaPointCell (qmaGridPort p a) = p :=
  qmaGridPort_cell p a

noncomputable section
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem chain_cell_positive (e : G.Edge) (k : ℕ) (hk : k ≤ 2*P.length e+1) :
    0 < (qmaPointCell (qmaPortChain (P.point e) (P.length e) k)).1 ∧
    0 < (qmaPointCell (qmaPortChain (P.point e) (P.length e) k)).2 := by
  by_cases h0 : k = 0
  · subst k
    simpa only [qmaPortChain_zero,qmaPointCell_center] using P.positive e 0 (Nat.zero_le _)
  by_cases hlast : k = 2*P.length e+1
  · subst k
    simpa only [qmaPortChain_last,qmaPointCell_center] using P.positive e (P.length e) le_rfl
  rw [qmaPortChain_inner (P.point e) (by omega) (by omega)]
  change 0 < (qmaPointCell (qmaGridPort (P.point e (k/2)) _)).1 ∧
    0 < (qmaPointCell (qmaGridPort (P.point e (k/2)) _)).2
  rw [qmaPointCell_port]
  exact P.positive e (k/2) (by omega)

theorem graph_cell_positive {x y : ℕ × ℕ} (h : P.graph.Adj x y) :
    (0 < (qmaPointCell x).1 ∧ 0 < (qmaPointCell x).2) ∧
    (0 < (qmaPointCell y).1 ∧ 0 < (qmaPointCell y).2) := by
  change _ ≠ _ ∧ _ at h
  rcases h.2 with ⟨e,k,hk,hl,hr⟩ | ⟨e,k,hk,hl,hr⟩
  · rw [← hl,← hr]
    exact ⟨P.chain_cell_positive e k hk.le,P.chain_cell_positive e (k+1) (by omega)⟩
  · rw [← hl,← hr]
    exact ⟨P.chain_cell_positive e (k+1) (by omega),P.chain_cell_positive e k hk.le⟩

theorem finished_port_cell_positive (N : ℚ) (D : ℕ) (v : Fin (P.finishedGraph N D).n)
    {p : ℕ × ℕ} {a : Fin 4} (hv : P.finishedPosition N D v = qmaGridPort p a) :
    0 < p.1 ∧ 0 < p.2 := by
  have h := P.toEmbedding.iterate_occupied_source N D (Or.inl ⟨v,hv⟩)
  rcases h with ⟨w,hw⟩ | ⟨e,k,hk,he⟩
  · exact (qmaGridPort_ne_center p (P.position w) a hw.symm).elim
  · have hp := P.chain_cell_positive e k hk
    change qmaPortChain (P.point e) (P.length e) k = qmaGridPort p a at he
    simpa only [he,qmaPointCell_port] using hp

end QMAPortRouteData
end
end ContinuumCoulomb

end OAI
