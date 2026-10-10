import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRetainedGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellRouteCatalog

namespace OAI

/-! Assign an actual short lattice path to every retained physical interaction. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaGridNeighborIndex_opposite {p q : ℕ × ℕ}
    (hp : 0 < p.1 ∧ 0 < p.2) (ha : qmaSquareGrid.Adj p q) :
    qmaGridNeighborIndex q p = qmaPortOpposite (qmaGridNeighborIndex p q) := by
  obtain ⟨a,rfl⟩ := qmaGridNeighbor_exists ha
  rcases p with ⟨x,y⟩
  have hx : x-1+1 = x := by omega
  have hy : y-1+1 = y := by omega
  fin_cases a <;> dsimp [qmaGridNeighborIndex,qmaGridNeighbor,qmaPortOpposite]
  all_goals split_ifs <;> first | rfl | omega

theorem qmaMovedPort_local (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    (p : ℕ × ℕ) (a : Fin 4) :
    qmaMovedPort cross p a = qmaCellTranslate p (qmaLocalPort (decide (cross p)) a) := by
  by_cases h : cross p
  · simp only [qmaMovedPort,qmaLocalPort,h,decide_true,ite_true,qmaCellTranslate_inner]
  · simp only [qmaMovedPort,qmaLocalPort,h,decide_false,Bool.false_eq_true,ite_false,qmaCellTranslate_port]

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def RoutingAllowed : QMACellRouteBody → Prop
  | .ray p _ => (∃ v, P.position v = p) ∧ ¬P.IsCrossing p
  | .pair p e => ¬P.IsCrossing p ∧ ∃ i : P.Interior, P.cell i = p ∧
      s(P.port i 0,P.port i 1) = s(qmaCellPairLeft e,qmaCellPairRight e)
  | .patch p _ => P.IsCrossing p
  | .corridor p a b c => b = decide (P.IsCrossing p) ∧
      c = decide (P.IsCrossing (qmaGridNeighbor p a))

theorem geometry_route_exists {x y : ℕ × ℕ} (h : P.RetainedGeometry x y) :
    ∃ R : QMACellRoute, P.RoutingAllowed R.body ∧ R.Valid ∧ R.source = x ∧ R.target = y := by
  rcases h with ⟨p,a,hsource,hn,⟨hx,hy⟩ | ⟨hx,hy⟩⟩ | ⟨p,a,b,hn,hx,hy,i,hi,hv⟩ |
    ⟨p,q,hpq,hp,_,hx,hy⟩
  · exact ⟨⟨.ray p a,false⟩,⟨hsource,hn⟩,trivial,hx.symm,hy.symm⟩
  · exact ⟨⟨.ray p a,true⟩,⟨hsource,hn⟩,trivial,hx.symm,hy.symm⟩
  · have hab : a ≠ b := by
      intro h
      rcases hv with ⟨h0,h1⟩ | ⟨h0,h1⟩
      · exact (by decide : (0 : Fin 2) ≠ 1) (P.port_injective i (h0.trans (h.trans h1.symm)))
      · exact (by decide : (0 : Fin 2) ≠ 1) (P.port_injective i (h0.trans (h.symm.trans h1.symm)))
    have hpair : s(P.port i 0,P.port i 1) = s(a,b) := by
      rcases hv with ⟨h0,h1⟩ | ⟨h0,h1⟩
      · rw [h0,h1]
      · rw [h0,h1]
        exact Sym2.eq_swap
    obtain ⟨e,he⟩ := qmaCellPair_complete a b hab
    rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · refine ⟨⟨.pair p e,false⟩,⟨hn,i,hi,?_⟩,trivial,?_,?_⟩
      · simpa only [ha,hb] using hpair
      · change qmaGridPort p (qmaCellPairLeft e) = x
        rw [← ha,← hx]
      · change qmaGridPort p (qmaCellPairRight e) = y
        rw [← hb,← hy]
    · refine ⟨⟨.pair p e,true⟩,⟨hn,i,hi,?_⟩,trivial,?_,?_⟩
      · rw [ha,hb] at hpair
        exact hpair.trans Sym2.eq_swap
      · change qmaGridPort p (qmaCellPairRight e) = x
        rw [← ha,← hx]
      · change qmaGridPort p (qmaCellPairLeft e) = y
        rw [← hb,← hy]
  · let a := qmaGridNeighborIndex p q
    refine ⟨⟨.corridor p a (decide (P.IsCrossing p)) (decide (P.IsCrossing q)),false⟩,
      ⟨rfl,?_⟩,hp,?_,?_⟩
    · rw [qmaGridNeighborIndex_spec hp.1 hp.2 hpq]
    · exact (qmaMovedPort_local P.IsCrossing p a).symm.trans hx.symm
    · change qmaCellTranslate (qmaGridNeighbor p a)
        (qmaLocalPort (decide (P.IsCrossing q)) (qmaPortOpposite a)) = y
      rw [qmaGridNeighborIndex_spec hp.1 hp.2 hpq,← qmaGridNeighborIndex_opposite hp hpq]
      exact (qmaMovedPort_local P.IsCrossing q (qmaGridNeighborIndex q p)).symm.trans hy.symm

def retainedRoute (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.portCrossingSelection N hD).retained.Edge) : QMACellRoute :=
  Classical.choose (P.geometry_route_exists (P.retained_geometry N hD havoid e))

theorem retainedRoute_spec (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.portCrossingSelection N hD).retained.Edge) :
    P.RoutingAllowed (P.retainedRoute N hD havoid e).body ∧
    (P.retainedRoute N hD havoid e).Valid ∧
    (P.retainedRoute N hD havoid e).source =
      P.movedPosition N D ((P.finishedGraph N D).left e.val) ∧
    (P.retainedRoute N hD havoid e).target =
      P.movedPosition N D ((P.finishedGraph N D).right e.val) :=
  Classical.choose_spec (P.geometry_route_exists (P.retained_geometry N hD havoid e))

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
