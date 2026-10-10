import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPhysicalEndpointCover
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellRouteSupport

namespace OAI

/-! Every physical spin retains the coarse cell of an original route point.
This transfers the original positive-coordinate and rectangle bounds. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical

@[simp] theorem qmaPointCell_inner (p : ℕ × ℕ) (a : Fin 4) :
    qmaPointCell (qmaInnerPort p a) = p := qmaInnerPort_cell p a

@[simp] theorem qmaPointCell_ancilla (p : ℕ × ℕ) (a : Fin 2) :
    qmaPointCell (qmaGadgetAncilla p a) = p := qmaGadgetAncilla_cell p a

theorem qmaCrossingMove_cell (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    {z : ℕ × ℕ} (hz : QMAPortPoint z) : qmaPointCell (qmaCrossingMove cross z) = qmaPointCell z := by
  rcases hz with ⟨p,rfl⟩ | ⟨p,a,rfl⟩
  · rw [qmaCrossingMove_center]
  · rw [qmaCrossingMove_port,qmaPointCell_port]
    split_ifs <;> simp only [qmaPointCell_inner,qmaPointCell_port]

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem chain_cell_property (Q : (ℕ × ℕ) → Prop)
    (hQ : ∀ e k, k ≤ P.length e → Q (P.point e k))
    (e : G.Edge) (k : ℕ) (hk : k ≤ 2*P.length e+1) :
    Q (qmaPointCell (qmaPortChain (P.point e) (P.length e) k)) := by
  by_cases h0 : k = 0
  · subst k
    simpa only [qmaPortChain_zero,qmaPointCell_center] using hQ e 0 (Nat.zero_le _)
  by_cases hlast : k = 2*P.length e+1
  · subst k
    simpa only [qmaPortChain_last,qmaPointCell_center] using hQ e (P.length e) le_rfl
  rw [qmaPortChain_inner (P.point e) (by omega) (by omega)]
  change Q (qmaPointCell (qmaGridPort (P.point e (k/2)) _))
  rw [qmaPointCell_port]
  exact hQ e (k/2) (by omega)

theorem finished_cell_property (Q : (ℕ × ℕ) → Prop)
    (hsource : ∀ v, Q (P.position v)) (hpath : ∀ e k, k ≤ P.length e → Q (P.point e k))
    (N : ℚ) (D : ℕ) (v : Fin (P.finishedGraph N D).n) : Q (qmaPointCell (P.finishedPosition N D v)) := by
  have h := P.toEmbedding.iterate_occupied_source N D (Or.inl ⟨v,rfl⟩)
  rcases h with ⟨w,hw⟩ | ⟨e,k,hk,he⟩
  · change qmaExpandedPoint (P.position w) = P.finishedPosition N D v at hw
    rw [← hw,qmaPointCell_center]
    exact hsource w
  · change qmaPortChain (P.point e) (P.length e) k = P.finishedPosition N D v at he
    rw [← he]
    exact P.chain_cell_property Q hpath e k hk

theorem crossingPosition_cell_property (Q : (ℕ × ℕ) → Prop)
    (hsource : ∀ v, Q (P.position v)) (hpath : ∀ e k, k ≤ P.length e → Q (P.point e k))
    (N : ℚ) (D : ℕ) (v : Fin ((P.finishedGraph N D).n+P.crossingCells.card*2)) :
    Q (qmaPointCell (P.crossingPosition N D v)) := by
  obtain ⟨v,rfl⟩ := (vertexEquiv (P.finishedGraph N D).n P.crossingCells.card).surjective v
  rcases v with v | ⟨i,a⟩
  · change Q (qmaPointCell (P.crossingPosition N D (old _ _ v)))
    rw [P.crossingPosition_old]
    change Q (qmaPointCell (qmaCrossingMove P.IsCrossing (P.finishedPosition N D v)))
    have hv : QMAPortPoint (P.finishedPosition N D v) := P.iterate_position_kind N D v
    rw [qmaCrossingMove_cell P.IsCrossing hv]
    exact P.finished_cell_property Q hsource hpath N D v
  · change Q (qmaPointCell (P.crossingPosition N D (fresh _ _ i a)))
    rw [P.crossingPosition_fresh]
    change Q (qmaPointCell (qmaGadgetAncilla (P.crossingCell i).val a))
    rw [qmaPointCell_ancilla]
    obtain ⟨j,k,hjk,hj,hk,hpair⟩ := P.mem_crossingCells.mp (P.crossingCell i).property
    rw [← hj]
    exact hpath j.1 (j.2.val+1) (P.cell_index_lt j).le

theorem crossingPosition_positive
    (hsource : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)
    (N : ℚ) (D : ℕ) (v : Fin ((P.finishedGraph N D).n+P.crossingCells.card*2)) :
    0 < (qmaPointCell (P.crossingPosition N D v)).1 ∧
    0 < (qmaPointCell (P.crossingPosition N D v)).2 :=
  P.crossingPosition_cell_property (fun p => 0 < p.1 ∧ 0 < p.2) hsource P.positive N D v

theorem crossingPosition_bounded {X Y : ℕ}
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e k, k ≤ P.length e → (P.point e k).1 < X ∧ (P.point e k).2 < Y)
    (N : ℚ) (D : ℕ) (v : Fin ((P.finishedGraph N D).n+P.crossingCells.card*2)) :
    (P.crossingPosition N D v).1 < 32*X ∧ (P.crossingPosition N D v).2 < 32*Y := by
  have h := P.crossingPosition_cell_property (fun p => p.1 < X ∧ p.2 < Y) hsource hpath N D v
  change (P.crossingPosition N D v).1/32 < X ∧ (P.crossingPosition N D v).2/32 < Y at h
  omega

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
