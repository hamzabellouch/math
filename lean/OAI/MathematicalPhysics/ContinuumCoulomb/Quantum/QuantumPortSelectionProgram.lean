import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSelectCorrectness
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortCrossingSelection

namespace OAI

/-! The endpoint scan uses the exact canonical crossing couplings of the
completed physical port graph. Disjoint terminal sets discharge uniqueness. -/

noncomputable section
namespace ContinuumCoulomb.QMAPortRouteData
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem crossingSiteFin_global (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) :
    Function.Injective (fun p : Fin P.crossingCells.card × Fin 4 =>
      P.crossingSiteFin N hD p.1 p.2) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hp : (P.crossingCell i,qmaPatchDirection a)=(P.crossingCell j,qmaPatchDirection b) :=
    P.crossingSite_injective N hD h
  have hi : P.crossingCell i=P.crossingCell j :=
    congrArg (fun x : P.Crossing × Fin 4 => x.1) hp
  have hij : i=j := P.crossingCells.equivFin.symm.injective hi
  have hab : a=b := qmaPatchDirection_injective
    (congrArg (fun x : P.Crossing × Fin 4 => x.2) hp)
  exact Prod.ext hij hab

theorem portCrossing_tag_iff (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (e : (P.finishedGraph N D).Edge) (i : Fin P.crossingCells.card) (a : Fin 2) :
    (P.portCrossingSelection N hD).tag e=some (i,a) ↔
      (P.finishedGraph N D).CrossingMatch (P.crossingSiteFin N hD) e (i,a) :=
  (P.finishedGraph N D).crossingTag_some_iff (P.crossingSiteFin N hD)
    (P.crossingSiteFin_global N hD) e (i,a)

theorem scanned_crossings (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    {m : ℕ} (labels : (P.finishedGraph N D).Edge ≃ Fin m) :
    QuantumCrossingSelectProgram.crossings
      (QuantumListGraph.packed (P.finishedGraph N D) labels,
        List.ofFn (QuantumCrossingSelectProgram.encodedSites (P.crossingSiteFin N hD))) =
      List.ofFn (QuantumCrossingListLayer.actualCrossing (P.portCrossingSelection N hD).layer) :=
  QuantumCrossingSelectProgram.crossings_selected (P.portCrossingSelection N hD)
    (P.portCrossing_tag_iff N hD) labels

end ContinuumCoulomb.QMAPortRouteData

end

end OAI
