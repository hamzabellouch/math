import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvenTapeProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRouteLattice
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListMergeMatrix

namespace OAI

/-! Literal fixed-round routing to the serialized square-lattice source. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFinalRoutingProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode MediatorListProgram

abbrev Input := QuantumSpatialPortProgram.Input × (ℚ × ℚ)
def inputCode : Input → List Bool := prodCode QuantumSpatialPortProgram.inputCode
  (prodCode ratCode ratCode)
def planar (A D : ℕ) (x : Input) : QuantumPlanarTapeProgram.Output :=
  QuantumPlanarTapeProgram.value (QuantumSpatialCrossingProgram.value A D x.1)
def even (A D : ℕ) (x : Input) : QuantumListRouteProgram.State :=
  QuantumEvenTapeProgram.value (x.1.1,planar A D x)
private opaque roundsValue : {k : ℕ // k=80} := ⟨80,rfl⟩
def rounds : ℕ := roundsValue.val
theorem rounds_eq : rounds=80 := roundsValue.property
def routed (A D : ℕ) (x : Input) : QuantumListRouteProgram.State :=
  QuantumListRouteProgram.iterate x.1.1 rounds (even A D x)
def value (A D : ℕ) (x : Input) : BinaryHeisenberg :=
  QuantumListRouteProgram.latticeOutput (routed A D x) x.2.1 x.2.2

noncomputable opaque spatialInputProgram : Procedure inputCode
    QuantumSpatialPortProgram.inputCode Prod.fst := Procedure.first _ _
noncomputable opaque thresholdsProgram : Procedure inputCode (prodCode ratCode ratCode) Prod.snd :=
  Procedure.second _ _
noncomputable opaque precisionProgram : Procedure inputCode ratCode (fun x => x.1.1) :=
  (Procedure.first ratCode QuantumForkGridProgram.preparedCode).comp spatialInputProgram
noncomputable opaque planarProgram (A D : ℕ) : Procedure inputCode
    QuantumPlanarTapeProgram.outputCode (planar A D) :=
  QuantumPlanarTapeProgram.program.comp
    ((QuantumSpatialCrossingProgram.program A D).comp spatialInputProgram)
noncomputable opaque evenProgram (A D : ℕ) : Procedure inputCode
    QuantumListRouteProgram.stateCode (even A D) :=
  QuantumEvenTapeProgram.program.comp (precisionProgram.pair (planarProgram A D))
noncomputable opaque routedProgram (A D : ℕ) : Procedure inputCode
    QuantumListRouteProgram.stateCode (routed A D) :=
  (QuantumListRouteProgram.iterateProgram rounds).comp (precisionProgram.pair (evenProgram A D))
noncomputable opaque program (A D : ℕ) : Procedure inputCode binaryHeisenbergCodec.encode
    (value A D) :=
  QuantumListRouteProgram.latticeOutputProgram.comp ((routedProgram A D).pair thresholdsProgram)

private theorem planar_value_bounded (x : QuantumPlanarTapeProgram.Input) :
    SourceBondLists.bounded (QuantumPlanarTapeProgram.value x).1.1
      (QuantumPlanarTapeProgram.value x).1.2.1 :=
  QuantumListMerge.bounded _ _

theorem planar_bounded (A D : ℕ) (x : Input) :
    SourceBondLists.bounded (planar A D x).1.1 (planar A D x).1.2.1 :=
  planar_value_bounded (QuantumSpatialCrossingProgram.value A D x.1)

theorem even_valid (A D : ℕ) (x : Input) :
    QuantumListSchedule.Valid (even A D x).1 :=
  QuantumEvenTapeProgram.value_valid _ (planar_bounded A D x)

theorem routed_valid (A D : ℕ) (x : Input) :
    QuantumListSchedule.Valid (routed A D x).1 := by
  rw [routed,QuantumListRouteProgram.iterate_state]
  exact QuantumListSchedule.iterate_valid x.1.1 _ (even_valid A D x) rounds

theorem energy_error (A D : ℕ) (x : Input) (hN : 0<x.1.1)
    (hn : ∀ e ∈ (planar A D x).1.2.1, e.1≠e.2.1) :
    |QuantumListSchedule.energy (routed A D x).1-
      sourceMatrixBottom (planar A D x).1.1
        (SourceBondLists.matrix (planar A D x).1.1 (planar A D x).1.2.1+
          ((planar A D x).1.2.2:ℂ) • 1)| ≤ 81/(x.1.1:ℝ) := by
  have hi := QuantumListSchedule.iterate_energy_error hN (even A D x).1 (even_valid A D x) rounds
  rw [← QuantumListRouteProgram.iterate_state] at hi
  rw [show (rounds:ℝ)=80 by exact_mod_cast rounds_eq] at hi
  have he := QuantumEvenTapeProgram.value_energy_error (x.1.1,planar A D x)
    (planar_bounded A D x) hn hN
  calc
    _ ≤ |QuantumListSchedule.energy (routed A D x).1-
          QuantumListSchedule.energy (even A D x).1|+
        |QuantumListSchedule.energy (even A D x).1-
          sourceMatrixBottom (planar A D x).1.1
            (SourceBondLists.matrix (planar A D x).1.1 (planar A D x).1.2.1+
              ((planar A D x).1.2.2:ℂ) • 1)| := abs_sub_le _ _ _
    _ ≤ 80/(x.1.1:ℝ)+1/(x.1.1:ℝ) := add_le_add hi he
    _ = _ := by ring

noncomputable def certificate (A D : ℕ) : Turing.TM2ComputableInPolyTime inputCode
    binaryHeisenbergCodec.encode (value A D) := (program A D).toTM2

end ContinuumCoulomb.QuantumFinalRoutingProgram

end

end OAI
