import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMergedOutputRoutes
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathScheduleSize

namespace OAI

/-! The actual crossing output has linear size when the coarse route length is
bounded by a fixed constant. Merging parallel edges can only decrease it. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem finished_size (N : ℚ) (D : ℕ) :
    (P.finishedGraph N D).n + Fintype.card (P.finishedGraph N D).Edge ≤
      5^D*(G.n+Fintype.card G.Edge) := P.schedule.iterate_size N D

theorem crossingOutput_size (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) :
    (P.crossingOutput N hD).n + Fintype.card (P.crossingOutput N hD).Edge ≤
      (5^D+11*D)*(G.n+Fintype.card G.Edge) := by
  have hs := P.finished_size N D
  have hc := P.crossingCells_card_le hD
  have hr : Fintype.card (P.portCrossingSelection N hD).retained.Edge ≤
      Fintype.card (P.finishedGraph N D).Edge := Fintype.card_subtype_le _
  have he := (P.portCrossingSelection N hD).layer.output_edge_count N
  change Fintype.card (P.crossingOutput N hD).Edge =
    Fintype.card (P.portCrossingSelection N hD).retained.Edge+9*P.crossingCells.card at he
  change (P.finishedGraph N D).n+P.crossingCells.card*2+
    Fintype.card (P.crossingOutput N hD).Edge ≤ _
  rw [he]
  nlinarith

theorem mergedOutput_size (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) :
    (P.crossingOutput N hD).merge.n + Fintype.card (P.crossingOutput N hD).merge.Edge ≤
      (5^D+11*D)*(G.n+Fintype.card G.Edge) :=
  (Nat.add_le_add_left (P.crossingOutput N hD).merge_edge_count _).trans
    (P.crossingOutput_size N hD)

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
