import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellPassages
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortLinks
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathCoverageReverse

namespace OAI

/-! Final physical spins lie at original centers or ports, and every occupied
internal port is represented by an actual physical spin. -/

noncomputable section
namespace ContinuumCoulomb

theorem qmaPortChain_kind (p : ℕ → ℕ × ℕ) (L k : ℕ) :
    (∃ q, qmaPortChain p L k = qmaExpandedPoint q) ∨
      ∃ q a, qmaPortChain p L k = qmaGridPort q a := by
  by_cases h0 : k = 0
  · subst k
    exact Or.inl ⟨p 0,qmaPortChain_zero p L⟩
  by_cases hL : k = 2*L+1
  · subst k
    exact Or.inl ⟨p L,qmaPortChain_last p L⟩
  · exact Or.inr ⟨p (k/2),qmaGridNeighborIndex (p (k/2)) (p (qmaPortNeighborIndex k)),
      by simp [qmaPortChain,h0,hL,qmaRoutePort,qmaDirectedPort]⟩

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem cell_port_chain (i : P.Interior) (a : Fin 2) :
    qmaPortChain (P.point i.1) (P.length i.1) (2*(i.2.val+1)+a.val) =
      qmaGridPort (P.cell i) (P.port i a) := by
  have hi := P.cell_index_lt i
  have ha := a.isLt
  rw [qmaPortChain_inner _ (by omega) (by omega)]
  fin_cases a
  · simp only [Nat.add_zero,qmaRoutePort_even,Nat.add_sub_cancel]
    rfl
  · rw [qmaRoutePort_odd]
    rfl

theorem iterate_covers_port (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (i : P.Interior) (a : Fin 2) :
    ∃ v, (P.toEmbedding.iterate N D).position v = qmaGridPort (P.cell i) (P.port i a) := by
  have hi := P.cell_index_lt i
  have ha := a.isLt
  have hb : 2*(i.2.val+1)+a.val ≤ 2*P.length i.1+1 := by omega
  obtain ⟨v,hv⟩ := P.toEmbedding.iterate_covers_point N hD i.1 (2*(i.2.val+1)+a.val) hb
  exact ⟨v,hv.trans (P.cell_port_chain i a)⟩

theorem iterate_position_kind (N : ℚ) (D : ℕ) (v : Fin (P.schedule.iterate N D).graph.n) :
    (∃ p, (P.toEmbedding.iterate N D).position v = qmaExpandedPoint p) ∨
      ∃ p a, (P.toEmbedding.iterate N D).position v = qmaGridPort p a := by
  have h := P.toEmbedding.iterate_occupied_source N D (Or.inl ⟨v,rfl⟩)
  rcases h with ⟨w,hw⟩ | ⟨e,k,_,hk⟩
  · exact Or.inl ⟨P.position w,hw.symm⟩
  · rw [← hk]
    exact qmaPortChain_kind (P.point e) (P.length e) k

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
