import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryToUnary
import OAI.Analysis.MatrixSigning.Machines.BinaryToUnaryDeterministic
import OAI.Analysis.MatrixSigning.Arithmetic.RationalComparePrimitives

namespace OAI

section

namespace KS.W03.InputHeaderPrimitives
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare

theorem copy_spec {K : ℕ} (ports : Fin 3 ↪ Fin K) (before : Fin K → List Bool)
    (raw : List Bool) (hs : before (ports 0) = raw)
    (hd : before (ports 1) = []) (hw : before (ports 2) = []) :
    RunSpec (KS.W01.FixedCopy.program ports) before
      (Function.update before (ports 1) raw) (2 * raw.length + 2) := by
  intro bits hbits
  exact KS.W01.FixedCopy.run_copy_restore ports before raw bits hs hd hw hbits

def unaryProgram {K : ℕ} (ports : Fin 3 ↪ Fin K) : Program K :=
  KS.W29.FixedSequential.liftPorts KS.W03.BinaryToUnary.program ports

theorem unary_spec {K : ℕ} (ports : Fin 3 ↪ Fin K) (before : Fin K → List Bool)
    (raw : List Bool) (hs : before (ports 0) = raw)
    (hd : before (ports 1) = []) (hw : before (ports 2) = []) :
    RunSpec (unaryProgram ports) before
      (replacePorts ports before ![[], List.replicate (KS.W19.bitsValue raw) true, []])
      (4 * KS.W19.bitsValue raw + 4 * raw.length + 2) := by
  apply runSpec_liftPorts
  have hb : (fun i => before (ports i)) = ![raw, [], []] := by
    funext i
    fin_cases i <;> simp [hs, hd, hw]
  rw [hb]
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  have h := KS.W03.BinaryToUnary.run_input_linear raw bits (by omega)
  rw [KS.W03.BinaryToUnary.init_eq] at h
  exact h

end KS.W03.InputHeaderPrimitives

end

end OAI
