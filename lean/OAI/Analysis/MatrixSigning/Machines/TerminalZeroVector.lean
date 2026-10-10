import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedPortRunSpec
import OAI.Analysis.MatrixSigning.Machines.BinaryToUnary
import OAI.Analysis.MatrixSigning.Machines.BinaryToUnaryDeterministic
import OAI.Analysis.MatrixSigning.Machines.FixedCopyRestore
import OAI.Analysis.MatrixSigning.Encoding.ZeroArrayConstructor

namespace OAI

namespace KS.W19.TerminalZeroVector
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def copyPorts : Fin 3 ↪ Fin 35 := ⟨![26,0,16], by decide⟩
def unaryPorts : Fin 3 ↪ Fin 35 := ⟨![0,1,2], by decide⟩
def zeroPorts : Fin 3 ↪ Fin 35 := ⟨![1,0,23], by decide⟩
def copyProgram : Program 35 := KS.W01.FixedCopy.program copyPorts
def unaryProgram : Program 35 := liftPorts KS.W03.BinaryToUnary.program unaryPorts
def zeroProgram : Program 35 := liftPorts KS.W11.ZeroArrayConstructor.program zeroPorts
def program : Program 35 := compose copyProgram (compose unaryProgram zeroProgram)

def ticks (n : ℕ) : ℕ := 28*n + 6*(Computability.encodeNat n).length + 6

theorem zero_vector_spec (s : Fin 35 → List Bool) (n : ℕ)
    (hd : s 26 = Computability.encodeNat n)
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = [])
    (h16 : s 16 = []) (h23 : s 23 = []) :
    RunSpec program s (Function.update s 23 (KS.W11.ZeroArrayConstructor.zeroTape n)) (ticks n) := by
  have hc : RunSpec copyProgram s (Function.update s 0 (Computability.encodeNat n))
      (2*(Computability.encodeNat n).length+2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine
    intro bits hb
    exact KS.W01.FixedCopy.run_copy_restore copyPorts s (Computability.encodeNat n) bits hd h0 h16 hb
  have hu0 : RunSpec KS.W03.BinaryToUnary.program
      ![Computability.encodeNat n,[],[]] ![[],List.replicate n true,[]]
      (4*n+4*(Computability.encodeNat n).length+2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine
    intro bits hb
    have h := KS.W03.BinaryToUnary.run_input_linear (Computability.encodeNat n) bits
      (by simpa only [bitsValue_encodeNat] using hb.ge)
    simp only [KS.W03.BinaryToUnary.init_eq, KS.W03.BinaryToUnary.cfg,
      bitsValue_encodeNat] at h
    exact h
  have hu : RunSpec unaryProgram (Function.update s 0 (Computability.encodeNat n))
      (Function.update s 1 (List.replicate n true))
      (4*n+4*(Computability.encodeNat n).length+2) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ unaryPorts _ _ _ _ _ hu0
    · intro j; fin_cases j <;> simp [unaryPorts,h1,h2]
    · intro j; fin_cases j <;> simp [unaryPorts,h0,h2]
    · intro j hj
      have ha := hj 0
      have hb := hj 1
      change j ≠ 0 at ha
      change j ≠ 1 at hb
      simp [Function.update_of_ne,ha,hb]
  have hz0 := KS.W11.ZeroArrayConstructor.zero_spec_linear (List.replicate n true)
  simp only [List.length_replicate] at hz0
  have hz : RunSpec zeroProgram (Function.update s 1 (List.replicate n true))
      (Function.update s 23 (KS.W11.ZeroArrayConstructor.zeroTape n)) (24*n+2) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ zeroPorts _ _ _ _ _ hz0
    · intro j; fin_cases j <;> simp [zeroPorts,KS.W11.ZeroArrayConstructor.«stacks»,h0,h23]
    · intro j; fin_cases j <;> simp [zeroPorts,KS.W11.ZeroArrayConstructor.«stacks»,h0,h1]
    · intro j hj
      have ha := hj 0
      have hb := hj 2
      change j ≠ 1 at ha
      change j ≠ 23 at hb
      simp [Function.update_of_ne,ha,hb]
  have h := hc.compose (hu.compose hz)
  convert h using 1 <;> simp [program,ticks]; omega

end KS.W19.TerminalZeroVector

end OAI
