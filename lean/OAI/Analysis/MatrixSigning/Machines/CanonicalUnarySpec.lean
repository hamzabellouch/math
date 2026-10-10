import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryToUnary
import OAI.Analysis.MatrixSigning.Machines.BinaryToUnaryDeterministic

namespace OAI

namespace KS.W07
open KS.W29.FixedSequential KS.W03.MachineCombinators

theorem canonicalUnary_spec (n : ℕ) :
    RunSpec KS.W03.BinaryToUnary.program ![Computability.encodeNat n, [], []]
      ![[], List.replicate n true, []]
      (4*n + 4*(Computability.encodeNat n).length + 2) := by
  unfold KS.W03.BinaryToUnary.program
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine KS.W03.BinaryToUnary.machine
  intro bits hbits
  have h := KS.W03.BinaryToUnary.run_input_linear (Computability.encodeNat n) bits
      (by simpa only [KS.W19.bitsValue_encodeNat] using hbits.ge)
  simp only [KS.W03.BinaryToUnary.init_eq, KS.W03.BinaryToUnary.cfg,
    KS.W19.bitsValue_encodeNat] at h
  exact h

end KS.W07

end OAI
