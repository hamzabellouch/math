import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortInnerPair
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellCrossings

namespace OAI

/-! Edges wholly inside one port cell are exactly the two ports of a route visit. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem visit_of_forward_pair (e : G.Edge) (k : ℕ) (hk : k < 2*P.length e+1)
    (p : ℕ × ℕ) (a b : Fin 4)
    (hl : qmaPortChain (P.point e) (P.length e) k = qmaGridPort p a)
    (hr : qmaPortChain (P.point e) (P.length e) (k+1) = qmaGridPort p b) :
    ∃ i : P.Interior, P.cell i = p ∧ P.port i 0 = a ∧ P.port i 1 = b := by
  obtain ⟨t,ht0,ht,hp,ha,hb⟩ := qmaPortChain_inner_pair (P.point e) (P.step e) hk p a b hl hr
  let i : P.Interior := ⟨e,⟨t-1,by omega⟩⟩
  have h1 : t-1+1 = t := by omega
  have h2 : t-1+2*1 = t+1 := by omega
  refine ⟨i,?_,?_,?_⟩
  · simpa only [cell,i,h1] using hp
  · simpa only [port,cell,arm,armIndex,i,Fin.val_zero,Nat.mul_zero,Nat.add_zero,h1] using ha
  · simpa only [port,cell,arm,armIndex,i,Fin.val_one,h1,h2] using hb

theorem graph_inner_pair {p : ℕ × ℕ} {a b : Fin 4}
    (h : P.graph.Adj (qmaGridPort p a) (qmaGridPort p b)) :
    ∃ i : P.Interior, P.cell i = p ∧
      ((P.port i 0 = a ∧ P.port i 1 = b) ∨ (P.port i 0 = b ∧ P.port i 1 = a)) := by
  change _ ≠ _ ∧ _ at h
  rcases h.2 with ⟨e,k,hk,hl,hr⟩ | ⟨e,k,hk,hl,hr⟩
  · obtain ⟨i,hi,ha,hb⟩ := P.visit_of_forward_pair e k hk p a b hl hr
    exact ⟨i,hi,Or.inl ⟨ha,hb⟩⟩
  · obtain ⟨i,hi,hb,ha⟩ := P.visit_of_forward_pair e k hk p b a hl hr
    exact ⟨i,hi,Or.inr ⟨hb,ha⟩⟩

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
