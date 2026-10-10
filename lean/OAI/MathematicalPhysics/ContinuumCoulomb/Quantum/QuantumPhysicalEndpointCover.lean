import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPermittedEndpointAvoidance

namespace OAI

/-! Every physical spin is an endpoint of a permitted catalog path. This also
covers isolated source spins and supplies the no-interior-spin condition. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical

theorem qmaPatchRoute_source_ancilla (p : ℕ × ℕ) :
    (qmaPatchRoute p 0).source = qmaGadgetAncilla p 0 := by
  change (32*p.1+10+4,32*p.2+10+8) = (32*p.1+14,32*p.2+18)
  apply Prod.ext <;> omega

theorem qmaPatchRoute_target_ancilla (p : ℕ × ℕ) :
    (qmaPatchRoute p 0).target = qmaGadgetAncilla p 1 := by
  change (32*p.1+10+8,32*p.2+10+4) = (32*p.1+18,32*p.2+14)
  apply Prod.ext <;> omega

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem physical_endpoint_cover (N : ℚ) (D : ℕ)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (v : Fin ((P.finishedGraph N D).n+P.crossingCells.card*2)) :
    ∃ R : QMACellRoute, P.RoutingAllowed R.body ∧ R.Valid ∧ R.source = P.crossingPosition N D v := by
  obtain ⟨v,rfl⟩ := (vertexEquiv (P.finishedGraph N D).n P.crossingCells.card).surjective v
  rcases v with v | ⟨i,a⟩
  · change ∃ R : QMACellRoute, P.RoutingAllowed R.body ∧ R.Valid ∧
      R.source = P.crossingPosition N D (old _ _ v)
    rw [P.crossingPosition_old]
    rcases P.iterate_position_kind N D v with ⟨p,hp⟩ | ⟨p,a,hp⟩
    · change P.finishedPosition N D v = qmaExpandedPoint p at hp
      have hs := P.finished_center_source N D v hp
      have hn : ¬P.IsCrossing p := by
        obtain ⟨w,rfl⟩ := hs
        exact P.source_not_crossing havoid w
      refine ⟨⟨.ray p 0,false⟩,⟨hs,hn⟩,trivial,?_⟩
      change qmaExpandedPoint p = qmaCrossingMove P.IsCrossing (P.finishedPosition N D v)
      rw [hp,qmaCrossingMove_center]
    · change P.finishedPosition N D v = qmaGridPort p a at hp
      have hpos := P.finished_port_cell_positive N D v hp
      let b := decide (P.IsCrossing p)
      let c := decide (P.IsCrossing (qmaGridNeighbor p a))
      refine ⟨⟨.corridor p a b c,false⟩,⟨rfl,rfl⟩,hpos,?_⟩
      change qmaCellTranslate p (qmaLocalPort b a) =
        qmaCrossingMove P.IsCrossing (P.finishedPosition N D v)
      rw [hp,qmaCrossingMove_port]
      exact (qmaMovedPort_local P.IsCrossing p a).symm
  · change ∃ R : QMACellRoute, P.RoutingAllowed R.body ∧ R.Valid ∧
      R.source = P.crossingPosition N D (fresh _ _ i a)
    rw [P.crossingPosition_fresh]
    have hc : P.IsCrossing (P.crossingCell i).val :=
      P.mem_crossingCells.mp (P.crossingCell i).property
    fin_cases a
    · exact ⟨qmaPatchRoute (P.crossingCell i).val 0,hc,trivial,qmaPatchRoute_source_ancilla _⟩
    · refine ⟨(qmaPatchRoute (P.crossingCell i).val 0).reverse,hc,trivial,?_⟩
      rw [QMACellRoute.reverse_source]
      exact qmaPatchRoute_target_ancilla _

theorem mergedOutputRoute_avoids (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.crossingOutput N hD).merge.Edge) (v : Fin (P.crossingOutput N hD).n) :
    P.crossingPosition N D v ∉ ((P.mergedOutputRoute N hD havoid e).path.drop 1).dropLast := by
  obtain ⟨R,hR,hv,hpos⟩ := P.physical_endpoint_cover N D havoid v
  rw [← hpos]
  have he := P.mergedOutputRoute_spec N hD havoid e
  exact P.permitted_avoids_source havoid _ R he.1 hR he.2.1 hv

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
