import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathSchedule

namespace OAI

/-! Fixed-round routed subdivisions retain linear graph size. -/

noncomputable section
namespace ContinuumCoulomb.QMAPathSchedule

 theorem next_size (W : QMAPathSchedule) (N : ℚ) :
    (W.next N).graph.n + Fintype.card (W.next N).graph.Edge ≤
      5*(W.graph.n+Fintype.card W.graph.Edge) := by
  change W.graph.n+W.active.card*2+
    Fintype.card (W.graph.subdivide W.active (fun _ => false) N).Edge ≤ _
  rw [QMARationalExchangeGraph.subdivide_edge_count]
  have h := Finset.card_le_univ W.active
  omega

theorem iterate_size (W : QMAPathSchedule) (N : ℚ) (k : ℕ) :
    (W.iterate N k).graph.n + Fintype.card (W.iterate N k).graph.Edge ≤
      5^k*(W.graph.n+Fintype.card W.graph.Edge) := by
  induction k with
  | zero =>
    change W.graph.n+Fintype.card W.graph.Edge ≤ 5^0*(W.graph.n+Fintype.card W.graph.Edge)
    simp
  | succ k ih =>
    change ((W.iterate N k).next N).graph.n + Fintype.card ((W.iterate N k).next N).graph.Edge ≤ _
    exact ((W.iterate N k).next_size N).trans (by simpa [pow_succ,mul_assoc,mul_comm,
      mul_left_comm] using (Nat.mul_le_mul_left 5 ih))

end ContinuumCoulomb.QMAPathSchedule

end

end OAI
