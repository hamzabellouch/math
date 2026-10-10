import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSpatialComplete
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedCellProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelOutput

namespace OAI

/-! The computed spatial arrays use exactly the same sum/product enumeration
as the actual ordered Hamiltonian compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedCellTable
open QuantumOrderedCellProgram QuantumOrderedLabelTable QuantumOrderedSpatialComplete
open ExactQuantumFactoring.BitStackProgram
open QuantumRouteCode
variable {ι κ : Type} {n m : ℕ}

def table (q : Fin n ≃ ι) (e : Fin m ≃ κ) (cell : ι → Pair) (anchor : κ → Pair) : State :=
  (List.ofFn (fun i => cell (q i)),List.ofFn (fun i => anchor (e i)))

theorem value_table (d : ℕ) (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → Pair) (anchor : κ → Pair) :
    value d (table q e cell anchor)=
      table (nextQubit q e) (nextTerm e d) (extendCell cell anchor) (extendAnchor d anchor) := by
  apply Prod.ext
  · rw [show (value d (table q e cell anchor)).1=
        List.ofFn (Fin.append (fun i => cell (q i)) (fun i => anchor (e i))) from cells_ofFn d _ _]
    apply congrArg List.ofFn
    funext i
    obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n+m)).surjective i
    cases i <;> simp [nextQubit,extendCell,Fin.append]
  · change anchors d (List.ofFn (fun i => anchor (e i)))=List.ofFn _
    rw [anchors_ofFn]
    rw [← product_table (fun p : Fin m × Fin d => anchor (e p.1))]
    apply congrArg List.ofFn
    funext i
    rfl

def complete (x : State) : State := value 4 (value 7 (value 4 (value 7 (value 4 (value 4 x)))))

noncomputable def completeProgram : Procedure stateCode stateCode complete :=
  (program 4).comp ((program 7).comp ((program 4).comp ((program 7).comp
    ((program 4).comp (program 4)))))

theorem complete_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → Pair) (anchor : κ → Pair) :
    complete (table q e cell anchor)=
      table (QuantumOrderedLabelTable.qubits6 q e) (QuantumOrderedLabelTable.terms6 e)
        (cell6 cell anchor) (anchor6 anchor) := by
  unfold complete
  rw [value_table,value_table,value_table,value_table,value_table,value_table]
  rfl

end ContinuumCoulomb.QuantumOrderedCellTable

end

end OAI
