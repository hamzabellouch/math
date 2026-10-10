import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedCellTable

namespace OAI

/-! The raw four-spin compiler repeats each computed logical cell four times,
in exactly the order of its physical spin indices. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedRawCells
open QuantumOrderedCellProgram QuantumOrderedCellTable QuantumOrderedSpatialComplete
open QuantumOrderedLabelTable QuantumRouteCode
open ExactQuantumFactoring.BitStackProgram

def value (x : State) : List Pair := anchors 4 (complete x).1

noncomputable def program : Procedure stateCode (listCode pairCode) value :=
  (anchorsProgram 4).comp ((Procedure.first (listCode pairCode) (listCode pairCode)).comp completeProgram)

theorem four_ofFn {n : ℕ} (cell : Fin n → Pair) :
    anchors 4 (List.ofFn cell)=
      List.ofFn (fun i : Fin (n*4) => cell (finProdFinEquiv.symm i).1) := by
  rw [anchors_ofFn,← product_table (fun p : Fin n × Fin 4 => cell p.1)]

theorem value_table {ι κ : Type} {n m : ℕ} (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → Pair) (anchor : κ → Pair) :
    value (table q e cell anchor)=
      List.ofFn (fun i : Fin (finalCount n m*4) =>
        cell6 cell anchor (qubits6 q e (finProdFinEquiv.symm i).1)) := by
  unfold value
  rw [complete_table]
  exact four_ofFn _

end ContinuumCoulomb.QuantumOrderedRawCells

end

end OAI
