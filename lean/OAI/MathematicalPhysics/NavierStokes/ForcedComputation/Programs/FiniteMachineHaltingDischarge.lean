import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FixedInterpreter
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.MachineDecisionInput

namespace OAI

/-! Discharge of the finite-table undecidability input, using the fixed
universal interpreter and Mathlib's proved halting theorem. -/

namespace ForcedComputation

theorem finiteMachineHaltingUndecidable : FiniteMachineHaltingUndecidable := by
  rintro ⟨d, hd, hcorrect⟩
  obtain ⟨M, input, hi, hM⟩ := FiniteMachine.exists_fixed_universal_machine
  apply ComputablePred.halting_problem 0
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun c : Nat.Partrec.Code => d (M, input (Encodable.encode c)),
    hd.comp ((Computable.const M).pair (hi.comp Computable.encode)), ?_⟩
  funext c
  apply propext
  have h := (hcorrect (M, input (Encodable.encode c)) (hM _).1).trans (hM _).2
  simpa only [Denumerable.ofNat_encode] using h.symm

end ForcedComputation

end OAI
