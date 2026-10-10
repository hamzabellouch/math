import Mathlib
import OAI.Analysis.MatrixSigning.Machines.NormalizeOutput
import OAI.Analysis.MatrixSigning.Machines.MachineRoundTrip
import OAI.Analysis.MatrixSigning.Machines.FixedCopyRestore
import OAI.Analysis.MatrixSigning.Machines.BinaryAccumulator

namespace OAI

namespace KS.W03.MultiplicationBody

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.BinaryAccumulator KS.W03.BinaryMultiply

def registers (input xs operand acc copy scratch reverse : List Bool) : Fin 7 → List Bool :=
  ![input, xs, operand, acc, copy, scratch, reverse]

def copyPorts : Fin 3 ↪ Fin 7 := ⟨![2, 4, 5], by decide⟩
def addPorts : Fin 3 ↪ Fin 7 := ⟨![3, 4, 6], by decide⟩
def reversePorts : Fin 3 ↪ Fin 7 := ⟨![0, 3, 6], by decide⟩

def copyProgram : Program 7 := KS.W01.FixedCopy.program copyPorts

def addProgram : Program 7 := ofMachine (lift3 KS.W01.BinaryAdder.machine addPorts)

def reverseProgram : Program 7 := ofMachine (lift3 KS.W29.NormalizeOutput.machine reversePorts)

def shiftInstruction : Instruction 7 1 :=
  ⟨none, Vector.ofFn (fun j => if j = 2 then .push false else .stay)⟩

def shiftProgram : Program 7 :=
  ofMachine (compile (0 : Fin 1) (0 : Fin 7) (3 : Fin 7) (fun _ _ _ => shiftInstruction))

def body : Program 7 :=
  compose (compose (compose copyProgram addProgram) reverseProgram) shiftProgram

theorem copy_spec (input xs operand acc : List Bool) :
    RunSpec copyProgram (registers input xs operand acc [] [] [])
      (registers input xs operand acc operand [] []) (2 * operand.length + 2) := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  erw [KS.W01.FixedCopy.run_copy_restore copyPorts _ operand bits rfl rfl rfl hbits]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem add_spec (input xs operand acc : List Bool) :
    RunSpec addProgram (registers input xs operand acc operand [] [])
      (registers input xs operand [] [] [] (KS.W01.BinaryAdder.addBits false acc operand).reverse)
      (max acc.length operand.length + 1) := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  apply lift3_run_eq
  · have hp : project addPorts
        (⟨some 0, registers input xs operand acc operand [] []⟩ : Config 7 2) =
        KS.W01.BinaryAdder.cfg (some 0) acc operand [] := by
      change KS.W29.Config.mk (some (0 : Fin 2)) _ = KS.W29.Config.mk (some (0 : Fin 2)) _
      congr 1
      funext j
      fin_cases j <;> rfl
    erw [hp]
    have hr := KS.W01.BinaryAdder.run_add false acc operand [] bits hbits
    simp only [KS.W01.BinaryAdder.carryState, Bool.false_eq_true, ↓reduceIte,
      List.append_nil] at hr
    rw [hr]
    change KS.W29.Config.mk none _ = KS.W29.Config.mk none _
    congr 1
    funext j
    fin_cases j <;> rfl
  · intro j hj
    have h0 := hj 0
    have h1 := hj 1
    have h2 := hj 2
    fin_cases j <;> simp_all [registers, addPorts]

theorem reverse_spec (input xs operand result : List Bool) :
    RunSpec reverseProgram (registers input xs operand [] [] [] result.reverse)
      (registers input xs operand result [] [] []) (result.length + 1) := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  apply lift3_run_eq
  · have hp : project reversePorts
        (⟨some 2, registers input xs operand [] [] [] result.reverse⟩ : Config 7 3) =
        KS.W29.FrameDecoder.config (some 2) input [] result.reverse := by
      change KS.W29.Config.mk (some (2 : Fin 3)) _ = KS.W29.Config.mk (some (2 : Fin 3)) _
      congr 1
      funext j
      fin_cases j <;> rfl
    erw [hp, KS.W29.NormalizeOutput.run_reversed input result bits hbits]
    change KS.W29.Config.mk none _ = KS.W29.Config.mk none _
    congr 1
    funext j
    fin_cases j <;> rfl
  · intro j hj
    have h0 := hj 0
    have h1 := hj 1
    have h2 := hj 2
    fin_cases j <;> simp_all [registers, reversePorts]

theorem shift_spec (input xs operand acc : List Bool) :
    RunSpec shiftProgram (registers input xs operand acc [] [] [])
      (registers input xs (shift operand) acc [] [] []) 1 := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons b bs =>
    have hb : bs = [] := by apply List.length_eq_zero_iff.mp; simpa using hbits
    subst bs
    erw [Machine.run.eq_2, step_compile]
    change Config.mk none _ = Config.mk none _
    congr 1
    funext j
    fin_cases j <;> rfl

theorem body_spec (input xs operand acc : List Bool) :
    RunSpec body (registers input xs operand acc [] [] [])
      (registers input xs (shift operand) (KS.W01.BinaryAdder.addBits false acc operand) [] [] [])
      (bodyTicks operand acc) := by
  have h1 := (copy_spec input xs operand acc).compose (add_spec input xs operand acc)
  have h2 := h1.compose
    (reverse_spec input xs operand (KS.W01.BinaryAdder.addBits false acc operand))
  exact h2.compose (shift_spec input xs operand (KS.W01.BinaryAdder.addBits false acc operand))

end KS.W03.MultiplicationBody

end OAI
