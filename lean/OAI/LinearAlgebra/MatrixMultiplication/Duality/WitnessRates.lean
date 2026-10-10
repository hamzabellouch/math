import OAI.LinearAlgebra.MatrixMultiplication.Duality.WitnessEntropy
import OAI.LinearAlgebra.MatrixMultiplication.Duality.ScriptIndependence
import OAI.LinearAlgebra.MatrixMultiplication.Duality.TerminationIndependence
import OAI.LinearAlgebra.MatrixMultiplication.Duality.InformationSchedule

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitnessRates

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

open MatrixMultiplication.Foundation CompletionLabels CompletionLabels.TopologicalFlatten
open DualInformation DualCompletionLaws DualWitness

theorem nonincident_independent (n : Fin (1 + readable.depth))
    (hn : program.pair n.val = .yz) :
    ConditionalIndependent law (labelRecordOf program.labels n.val)
      (program.labels n.val) x := by
  exact DualProgramIndependence.termination_independent source readable laws288
    state288.rho
    (by rw [state288_rho]; exact rho288_range.1.le)
    (by rw [state288_rho]; exact rho288_range.2.le)
    DualProgramIndependence.laws288_independent n hn

theorem incident_rate : rate .xy + rate .xz = 288 * Real.log 2 := by
  let : Fintype (Coordinate Word Word Word .B) := inferInstanceAs (Fintype Word)
  have h := program.incident_rate_eq_x_entropy law program_complete PUnit.unit
    (fun _ => rfl) (fun n hn => nonincident_independent n hn)
  change rate .xy + rate .xz = finiteEntropy (law.map x).mass at h
  rw [x_entropy] at h
  exact h

theorem hidden_rate : rate .yz = 288 * hiddenRate := by
  linarith only [rate_sum, law_entropy, incident_rate]

end MatrixMultiplication.DualWitnessRates

end

end OAI
