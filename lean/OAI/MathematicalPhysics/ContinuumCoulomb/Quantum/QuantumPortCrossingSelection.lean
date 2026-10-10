import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSelectFromSites
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSites

namespace OAI

/-! Select and remove the actual finite crossing cells in a completed rational
port graph. The gadget terminals are existing physical spins. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaPatchDirection : Fin 4 → Fin 4 := ![2,1,0,3]

theorem qmaPatchDirection_injective : Function.Injective qmaPatchDirection := by decide

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def crossingCell (i : Fin P.crossingCells.card) : P.Crossing := P.crossingCells.equivFin.symm i

def crossingSiteFin (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (i : Fin P.crossingCells.card) (a : Fin 4) : Fin (P.finishedGraph N D).n :=
  P.crossingSite N hD (P.crossingCell i) (qmaPatchDirection a)

theorem crossingSiteFin_injective (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (i : Fin P.crossingCells.card) : Function.Injective (P.crossingSiteFin N hD i) := by
  intro a b h
  have he : (P.crossingCell i,qmaPatchDirection a) = (P.crossingCell i,qmaPatchDirection b) :=
    P.crossingSite_injective N hD h
  exact qmaPatchDirection_injective (congrArg (fun z : P.Crossing × Fin 4 => z.2) he)

def portCrossingSelection (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) :
    QMARationalCrossingSelection (P.finishedGraph N D) P.crossingCells.card :=
  (P.finishedGraph N D).crossingSelection (P.crossingSiteFin N hD) (P.crossingSiteFin_injective N hD)

theorem portCrossing_energy_error {N : ℚ} (hN : 0 < N) {D : ℕ} (hD : ∀ e, P.length e ≤ D) :
    |((P.portCrossingSelection N hD).layer.output N).energy-G.energy| ≤ ((D+1:ℕ):ℝ)/(N:ℝ) := by
  have h1 := (P.portCrossingSelection N hD).output_energy_error hN
  have h2 := P.schedule.iterate_energy_error hN D
  calc
    _ ≤ |((P.portCrossingSelection N hD).layer.output N).energy-(P.finishedGraph N D).energy| +
      |(P.finishedGraph N D).energy-G.energy| := abs_sub_le _ _ _
    _ ≤ 1/(N:ℝ)+(D:ℝ)/(N:ℝ) := add_le_add h1 h2
    _ = _ := by push_cast; ring

theorem crossingCells_card_le {D : ℕ} (hD : ∀ e, P.length e ≤ D) :
    P.crossingCells.card ≤ Fintype.card G.Edge*D := by
  calc
    _ ≤ ∑ e, (P.length e-1) := P.crossingCells_card
    _ ≤ ∑ _e : G.Edge, D := Finset.sum_le_sum (fun e _ => (Nat.sub_le _ _).trans (hD e))
    _ = _ := by simp

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
