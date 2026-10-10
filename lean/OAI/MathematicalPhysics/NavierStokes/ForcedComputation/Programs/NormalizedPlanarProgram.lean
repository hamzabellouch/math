import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarTranslation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarInitialShift

namespace OAI

/-! The finite Hamiltonian data for the prescribed initial particle. All
branches are translated by the same rational normalization, after adjoining
the fresh nonhalting initial state. -/

namespace ForcedComputation.Recorder.Planar
open ShearFlows PlanarHamiltonian PlanarRouting

def normalizedPulse (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (i : Fin (actions (freshMachine I.1) (freshInput_wellFormed hI)).length) : Pulse :=
  (compiledPulse (freshMachine I.1) (freshInput_wellFormed hI) i).translated
    (initialShift (freshInput I) (freshInput_valid hI))

theorem normalizedPulse_valid (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (i : Fin (actions (freshMachine I.1) (freshInput_valid hI).1).length) :
    (normalizedPulse I hI i).Valid :=
  Pulse.translated_valid _ (compiledPulse_valid _ _ i)

theorem normalizedPulse_inUnit (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (i : Fin (actions (freshMachine I.1) (freshInput_valid hI).1).length) :
    (normalizedPulse I hI i).InUnit := by
  let M := freshMachine I.1
  let hM := (freshInput_valid hI).1
  have hδ := initialShift_small_rat (freshInput I) (freshInput_valid hI)
    (fresh_initial_nonhalting I hI)
  apply Pulse.translated_inUnit _ (compiledPulse_inUnit M hM i)
    (Action.rectangle_between ((actions M hM).get i))
  · have hc := routingCollar_parking_bound M hM
    have hε := parkingScale_le (geometricBranches M hM).length
    change routingCollar M hM ≤ 1 / 65536
    linarith
  · intro j
    fin_cases j
    · change -(1 / 128 : ℚ) ≤ initialShift (freshInput I) (freshInput_valid hI) 0 ∧
        initialShift (freshInput I) (freshInput_valid hI) 0 ≤ 1 / 128
      obtain ⟨hl, hu⟩ := abs_le.mp hδ.1
      constructor <;> linarith
    · change -(1 / 128 : ℚ) ≤ initialShift (freshInput I) (freshInput_valid hI) 1 ∧
        initialShift (freshInput I) (freshInput_valid hI) 1 ≤ 1 / 128
      obtain ⟨hl, hu⟩ := abs_le.mp hδ.2
      constructor <;> linarith

def normalizedHamiltonian (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    FieldExpr := processorExpression (normalizedPulse I hI)

theorem normalizedHamiltonian_valid (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : (normalizedHamiltonian I hI).Valid :=
  processorExpression_valid (normalizedPulse_valid I hI)

theorem normalizedHamiltonian_noTime (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    SpatialExpression.NoTime (normalizedHamiltonian I hI) := processorExpression_noTime _

theorem normalizedHamiltonian_unitPeriods (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    SpatialExpression.UnitPeriods (normalizedHamiltonian I hI) := processorExpression_unitPeriods _

theorem normalizedHamiltonian_periodic (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    CubePeriodic 1 (SpatialExpression.spatialValue (normalizedHamiltonian I hI)) :=
  SpatialExpression.unitPeriods_periodic (normalizedHamiltonian_unitPeriods I hI)

end ForcedComputation.Recorder.Planar

end OAI
