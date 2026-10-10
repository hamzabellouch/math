import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialInputTape
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingFamily

namespace OAI

/-! The literal initial/fork program supplies the same source-center and
coarse-path arrays used by the actual lattice crossing construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialRoutingTape
open QuantumForkList ExactQuantumFactoring.BitStackProgram

def value (A D : ℕ) (x : QuantumForkGridProgram.PreparedInput) : QuantumPathTable.Input :=
  QuantumRoutingFamily.table (spatialDensity A D) (27*spatialDensity A D)
    (QuantumForkRoutingData.value (QuantumForkGridProgram.output D x))

noncomputable opaque program (A D : ℕ) :
    Procedure QuantumForkGridProgram.preparedCode QuantumPathTable.inputCode (value A D) :=
  (QuantumRoutingFamily.tableProgram (spatialDensity A D) (27*spatialDensity A D)).comp
    (QuantumForkRoutingData.program.comp (QuantumForkGridProgram.outputProgram D))

theorem value_actual {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) :
    value A D (QuantumSpatialInputTape.input I) =
      (List.ofFn I.model.placedVertex,
        List.ofFn (fun e : I.model.Term => (I.model.portRouteData hA I.model_degree).routeList e)) := by
  unfold value
  rw [QuantumSpatialInputTape.routing_eq]
  have h := QuantumRoutingFamily.table_actual I.model (Equiv.refl _) hA I.model_degree
  exact h

end ContinuumCoulomb.QuantumSpatialRoutingTape

end

end OAI
