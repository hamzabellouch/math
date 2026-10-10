import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedDotBody

namespace OAI

namespace KS.W12.FixedDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def pushDispatch (b : Bool) (_ : Fin 1) (_heads : Fin 19 → Fin 3) (_coin : Bool) :
    Instruction 19 1 :=
  ⟨none, Vector.ofFn (fun j => if j = 17 then .push b else .stay)⟩

def pushProgram (b : Bool) : Program 19 := ofMachine (compile 0 16 17 (pushDispatch b))

def pushAfter (b : Bool) (before : Fin 19 → List Bool) : Fin 19 → List Bool :=
  fun j => if j = 17 then b :: before j else before j

theorem push_spec (b : Bool) (before : Fin 19 → List Bool) :
    RunSpec (pushProgram b) before (pushAfter b before) 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
      have hr : rest = [] := by simpa using hbits
      subst rest
      refine (KS.W19.MachineTransport.run_ofMachine
        (compile (0 : Fin 1) (16 : Fin 19) 17 (pushDispatch b))
        (⟨some (0 : Fin 1), before⟩ : Config 19 1) [coin]).trans ?_
      simp only [Machine.run]
      refine (step_compile (0 : Fin 1) (16 : Fin 19) 17 (pushDispatch b)
        (0 : Fin 1) before coin).trans ?_
      change (Config.mk (none : Option (Fin 1)) _ : Config 19 1) = Config.mk none _
      apply congrArg (fun work : Fin 19 → List Bool =>
        (Config.mk (none : Option (Fin 1)) work : Config 19 1))
      funext j
      by_cases hj : j = 17
      · subst j
        simp [pushDispatch, pushAfter, Instruction.action, KS.W29.StackAction.apply]
      · simp [pushDispatch, pushAfter, Instruction.action, KS.W29.StackAction.apply, hj]

def «initialize» : Program 19 :=
  compose (compose (compose (compose (pushProgram true) (pushProgram true))
    (pushProgram false)) (pushProgram true)) (pushProgram false)

def initialStacks (source : List Bool) : Fin 19 → List Bool := registers source [] [] [] []

theorem initialize_spec (source : List Bool) :
    RunSpec «initialize» (initialStacks source) (boundary source 0) 5 := by
  let s0 := initialStacks source
  let s1 := pushAfter true s0
  let s2 := pushAfter true s1
  let s3 := pushAfter false s2
  let s4 := pushAfter true s3
  have h := ((((push_spec true s0).compose (push_spec true s1)).compose
    (push_spec false s2)).compose (push_spec true s3)).compose (push_spec false s4)
  have hz : KS.W01.encodeRat 0 = [false, true, false, true, true] := by decide
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> simp [s0, s1, s2, s3, s4, pushAfter, initialStacks, boundary, registers, hz]

def program : Program 19 := compose «initialize» (loopProgram body)
def machine : Machine := program.toMachine

def totalTicks (ps : List (ℚ × ℚ)) : ℕ := 5 + loopTicks bodyTicks ps 0

theorem full_spec (ps : List (ℚ × ℚ)) :
    RunSpec program (initialStacks (inputWire ps)) (boundary [] (dotValue ps)) (totalTicks ps) := by
  have h := (initialize_spec (inputWire ps)).compose (dot_loop_spec ps 0)
  simp only [zero_add] at h
  exact h

@[simp] theorem machine_stackCount : machine.stackCount = 19 := rfl
@[simp] theorem machine_inputStack : machine.inputStack = (16 : Fin 19) := rfl
@[simp] theorem machine_outputStack : machine.outputStack = (17 : Fin 19) := rfl

theorem init_eq (source : List Bool) :
    machine.init source = ⟨some program.initial, initialStacks source⟩ := by
  change Config.mk (some program.initial)
    (fun j : Fin 19 => if j = (16 : Fin 19) then source else []) =
      Config.mk (some program.initial) (initialStacks source)
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_input (ps : List (ℚ × ℚ)) (bits : List Bool) (hlen : totalTicks ps ≤ bits.length) :
    machine.run (machine.init (inputWire ps)) bits = ⟨none, boundary [] (dotValue ps)⟩ := by
  rw [init_eq]
  exact (full_spec ps).run_of_le bits hlen

theorem output_correct (ps : List (ℚ × ℚ)) (bits : List Bool)
    (hlen : totalTicks ps ≤ bits.length) :
    machine.output (inputWire ps) bits = KS.W01.encodeRat (dotValue ps) := by
  unfold Machine.output
  rw [run_input ps bits hlen]
  simp [machine_outputStack, boundary, registers]

theorem scratch_cleared (ps : List (ℚ × ℚ)) (bits : List Bool)
    (hlen : totalTicks ps ≤ bits.length) (j : Fin 19) (hj : j ≠ 17) :
    ((machine.run (machine.init (inputWire ps)) bits).«stacks» j) = [] := by
  rw [run_input ps bits hlen]
  simp [boundary, registers, hj]

theorem transient_payload (ps : List (ℚ × ℚ)) (bits : List Bool) (j : Fin 19) :
    ((machine.run (machine.init (inputWire ps)) bits).«stacks» j).length ≤
      (inputWire ps).length + bits.length := by
  have h := machine.run_stack_length_le (machine.init (inputWire ps)) bits j
  have hi : ((machine.init (inputWire ps)).«stacks» j).length ≤ (inputWire ps).length := by
    change (if j = (16 : Fin 19) then inputWire ps else []).length ≤ _
    split <;> simp
  exact h.trans (Nat.add_le_add_right hi _)

end KS.W12.FixedDot

end OAI
