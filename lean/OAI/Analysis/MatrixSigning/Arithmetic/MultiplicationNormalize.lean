import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.MultiplicationBody
import OAI.Analysis.MatrixSigning.Machines.BinaryTrimMachine

namespace OAI

namespace KS.W03.MultiplicationNormalize

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.MultiplicationBody

def reversePorts : Fin 3 ↪ Fin 7 := ⟨![0, 6, 3], by decide⟩
def trimPorts : Fin 3 ↪ Fin 7 := ⟨![0, 3, 6], by decide⟩

def reverseProgram : Program 7 := ofMachine (lift3 KS.W29.NormalizeOutput.machine reversePorts)
def trimProgram : Program 7 := ofMachine (lift3 KS.W19.BinaryTrimMachine.machine trimPorts)
def program : Program 7 := compose reverseProgram trimProgram

theorem reverse_spec (input xs operand raw : List Bool) :
    RunSpec reverseProgram (registers input xs operand raw [] [] [])
      (registers input xs operand [] [] [] raw.reverse) (raw.length + 1) := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  apply lift3_run_eq
  · have hp : project reversePorts
        (⟨some 2, registers input xs operand raw [] [] []⟩ : Config 7 3) =
        KS.W29.FrameDecoder.config (some 2) input [] raw := by
      change KS.W29.Config.mk (some (2 : Fin 3)) _ = KS.W29.Config.mk (some (2 : Fin 3)) _
      congr 1
      funext j
      fin_cases j <;> rfl
    erw [hp, KS.W29.NormalizeOutput.run_normalize input [] raw bits hbits]
    simp only [List.append_nil]
    change KS.W29.Config.mk none _ = KS.W29.Config.mk none _
    congr 1
    funext j
    fin_cases j <;> rfl
  · intro j hj
    have h0 := hj 0
    have h1 := hj 1
    have h2 := hj 2
    fin_cases j <;> simp_all [registers, reversePorts]

theorem trim_spec (input xs operand raw : List Bool) :
    RunSpec trimProgram (registers input xs operand [] [] [] raw.reverse)
      (registers input xs operand (Computability.encodeNat (KS.W19.bitsValue raw)) [] [] [])
      (raw.length + 1) := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  apply lift3_run_eq
  · have hp : project trimPorts
        (⟨some 0, registers input xs operand [] [] [] raw.reverse⟩ : Config 7 2) =
        KS.W19.BinaryTrimMachine.cfg (some 0) input [] raw.reverse := by
      change KS.W29.Config.mk (some (0 : Fin 2)) _ = KS.W29.Config.mk (some (0 : Fin 2)) _
      congr 1
      funext j
      fin_cases j <;> rfl
    erw [hp, KS.W19.BinaryTrimMachine.run_payload input raw bits hbits]
    change KS.W29.Config.mk none _ = KS.W29.Config.mk none _
    congr 1
    funext j
    fin_cases j <;> rfl
  · intro j hj
    have h0 := hj 0
    have h1 := hj 1
    have h2 := hj 2
    fin_cases j <;> simp_all [registers, trimPorts]

theorem normalize_spec (input xs operand raw : List Bool) :
    RunSpec program (registers input xs operand raw [] [] [])
      (registers input xs operand (Computability.encodeNat (KS.W19.bitsValue raw)) [] [] [])
      (2 * raw.length + 2) := by
  have h := (reverse_spec input xs operand raw).compose (trim_spec input xs operand raw)
  convert h using 1 <;> first | rfl | omega

@[simp] theorem output_port : program.output = 3 := rfl

end KS.W03.MultiplicationNormalize

end OAI
