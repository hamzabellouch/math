import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.MultiplicationBody

namespace OAI

section

namespace KS.W03.MultiplicationInitialize

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.MultiplicationBody

def firstPorts : Fin 3 ↪ Fin 7 := ⟨![0, 1, 6], by decide⟩
def secondPorts : Fin 3 ↪ Fin 7 := ⟨![0, 2, 6], by decide⟩

def firstProgram : Program 7 := ofMachine (lift3 KS.W29.FrameDecoder.machine firstPorts)
def secondProgram : Program 7 := ofMachine (lift3 KS.W29.FrameDecoder.machine secondPorts)
def program : Program 7 := compose firstProgram secondProgram

def inputBits (xs ys : List Bool) : List Bool := KS.W01.frame xs ++ KS.W01.frame ys

def ticks (xs ys : List Bool) : ℕ := (3 * xs.length + 2) + (3 * ys.length + 2)

theorem first_spec (xs ys : List Bool) :
    RunSpec firstProgram (registers (inputBits xs ys) [] [] [] [] [] [])
      (registers (KS.W01.frame ys) xs [] [] [] [] []) (3 * xs.length + 2) := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  apply lift3_run_eq
  · have hp : project firstPorts
        (⟨some 0, registers (inputBits xs ys) [] [] [] [] [] []⟩ : Config 7 3) =
        KS.W29.FrameDecoder.machine.init (KS.W01.frame xs ++ KS.W01.frame ys) := by
      change KS.W29.Config.mk (some (0 : Fin 3)) _ = KS.W29.Config.mk (some (0 : Fin 3)) _
      congr 1
      funext j
      fin_cases j <;> rfl
    erw [hp, KS.W29.FrameDecoder.run_frame xs (KS.W01.frame ys) bits hbits]
    change KS.W29.Config.mk none _ = KS.W29.Config.mk none _
    congr 1
    funext j
    fin_cases j <;> rfl
  · intro j hj
    have h0 := hj 0
    have h1 := hj 1
    have h2 := hj 2
    fin_cases j <;> simp_all [registers, firstPorts]

theorem second_spec (xs ys : List Bool) :
    RunSpec secondProgram (registers (KS.W01.frame ys) xs [] [] [] [] [])
      (registers [] xs ys [] [] [] []) (3 * ys.length + 2) := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  apply lift3_run_eq
  · have hp : project secondPorts
        (⟨some 0, registers (KS.W01.frame ys) xs [] [] [] [] []⟩ : Config 7 3) =
        KS.W29.FrameDecoder.machine.init (KS.W01.frame ys ++ []) := by
      simp only [List.append_nil]
      change KS.W29.Config.mk (some (0 : Fin 3)) _ = KS.W29.Config.mk (some (0 : Fin 3)) _
      congr 1
      funext j
      fin_cases j <;> rfl
    erw [hp, KS.W29.FrameDecoder.run_frame ys [] bits hbits]
    change KS.W29.Config.mk none _ = KS.W29.Config.mk none _
    congr 1
    funext j
    fin_cases j <;> rfl
  · intro j hj
    have h0 := hj 0
    have h1 := hj 1
    have h2 := hj 2
    fin_cases j <;> simp_all [registers, secondPorts]

theorem initialize_spec (xs ys : List Bool) :
    RunSpec program (registers (inputBits xs ys) [] [] [] [] [] [])
      (registers [] xs ys [] [] [] []) (ticks xs ys) :=
  (first_spec xs ys).compose (second_spec xs ys)

@[simp] theorem input_port : program.input = 0 := rfl

theorem inputBits_length (xs ys : List Bool) :
    (inputBits xs ys).length = 2 * (xs.length + ys.length) + 2 := by
  simp only [inputBits, List.length_append, KS.W01.length_frame]
  omega

end KS.W03.MultiplicationInitialize

end

end OAI
