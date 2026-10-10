import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryRoutedEnergy
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialFinalCount

namespace OAI

/-! The literal circuit compiler satisfies the original Heisenberg yes/no
promise. Its scalar shift and finite edge order are those of the emitted tape. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySourceProgram
open QuantumHistorySpatial QuantumHistoryPreparedProgram QuantumPaddedLabelProgram

theorem value_eq_latticeOutput (c : QMACircuit) :
    value c = QuantumListRouteProgram.latticeOutput (routedState c)
      (thresholds c).1 (thresholds c).2 := rfl

theorem routed_vertices_pos (c : QMACircuit) (hc : c.WellFormed) :
    0 < (routedState c).1.1 := by
  rw [routedState_actual c hc]
  exact (model_vertices_pos (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
    (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c)).trans_le
    (QuantumFinalRoutingProgram.spatial_count_le
      (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
        (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c))
      finalDensity_pos (precision c) (thresholds c).1 (thresholds c).2)

theorem routed_realization (c : QMACircuit) (hc : c.WellFormed) :
    ∃ (hs : QuantumListSchedule.Valid (routedState c).1)
      (Q : QMAPathEmbedding (QuantumListSchedule.schedule (routedState c).1 hs)),
      QuantumListRouteProgram.Represents (routedState c) hs Q ∧
      ∀ e, qmaSquareGrid.Adj
        (Q.position ((QuantumListSchedule.schedule (routedState c).1 hs).graph.left e))
        (Q.position ((QuantumListSchedule.schedule (routedState c).1 hs).graph.right e)) := by
  rw [routedState_actual c hc]
  obtain ⟨hs,Q,hQ,_,hgrid⟩ := QuantumFinalRoutingProgram.spatial_realization
    (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
      (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c))
    finalDensity_pos (N := (precision c : ℚ))
    (by exact_mod_cast precision_pos c) (thresholds c).1 (thresholds c).2
  exact ⟨hs,Q,hQ,hgrid⟩

theorem literal_valid (c : QMACircuit) (hc : c.WellFormed) : (value c).Valid := by
  rw [value_eq_latticeOutput]
  obtain ⟨hs,Q,hQ,hgrid⟩ := routed_realization c hc
  exact QuantumListRouteProgram.latticeOutput_valid _ hs Q hQ hgrid
    (routed_vertices_pos c hc) _ _ (thresholds_lt c)

theorem literal_accepting (c : QMACircuit) (hc : c.WellFormed) {k : ℕ}
    (hp : (value c).PolynomialPromise k)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (ha : 2/3 ≤ qmaAcceptance c hc psi) :
    value c ∈ (sourceHeisenbergPromise k).yes := by
  rw [value_eq_latticeOutput] at hp ⊢
  obtain ⟨hs,Q,hQ,hgrid⟩ := routed_realization c hc
  exact QuantumListRouteProgram.latticeOutput_yes _ hs Q hQ hgrid
    (routed_vertices_pos c hc) _ _ (thresholds_lt c) hp
    (routed_accepting c hc psi hpsi ha)

theorem literal_rejecting (c : QMACircuit) (hc : c.WellFormed) {k : ℕ}
    (hp : (value c).PolynomialPromise k)
    (ha : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3) :
    value c ∈ (sourceHeisenbergPromise k).no := by
  rw [value_eq_latticeOutput] at hp ⊢
  obtain ⟨hs,Q,hQ,hgrid⟩ := routed_realization c hc
  exact QuantumListRouteProgram.latticeOutput_no _ hs Q hQ hgrid
    (routed_vertices_pos c hc) _ _ (thresholds_lt c) hp
    (routed_rejecting c hc ha)

end ContinuumCoulomb.QuantumHistorySourceProgram

end

end OAI
