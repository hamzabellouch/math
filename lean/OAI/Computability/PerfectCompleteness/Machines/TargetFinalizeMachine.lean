import OAI.Computability.PerfectCompleteness.Machines.TargetHeaderMachine
import OAI.Computability.UniqueGames.Machines.MachineDrainManyLemmas

namespace OAI


namespace PerfectCompleteness.TargetFinalizeMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction.MachineTransfer
open MachineComposition

variable {K Λ A : Type} [DecidableEq K] {stackCount : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

def headerTape (tape : Fin 4 → K) : Fin 3 → K
  | 0 => tape 1
  | 1 => tape 2
  | 2 => tape 3

omit [DecidableEq K] in
theorem headerTape_injective (tape : Fin 4 → K) (distinct : Function.Injective tape) :
    Function.Injective (headerTape tape) := by
  intro i j same
  fin_cases i <;> fin_cases j <;> simp only [headerTape] at same ⊢ <;>
    first | rfl | exact False.elim (by simpa using distinct same)

abbrev WorkLabel (enumeration : Fin stackCount ≃ K) (output : K) :=
  MachineDrainMany.Label (MachineDrainMany.workTapes enumeration output)

inductive Label (Cleanup : Type)
  | reverse
  | header (label : TargetHeaderMachine.Label)
  | cleanup (label : Cleanup)
  | finish
  deriving DecidableEq, Fintype

abbrev Labels (enumeration : Fin stackCount ≃ K) (output : K) :=
  Label (WorkLabel enumeration output)

def instruction (q : Nat) (enumeration : Fin stackCount ≃ K) (tape : Fin 4 → K)
    (initial : A) (labels : Labels enumeration (tape 3) → Λ) :
    Labels enumeration (tape 3) → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .reverse => loopAt (tape 0) (tape 3) id false (labels .reverse)
      (some (labels (.header TargetHeaderMachine.main)))
  | .header label => TargetHeaderMachine.instruction q (headerTape tape)
      (fun l => labels (.header l))
      (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration (tape 3))
        (fun l => labels (.cleanup l)) (some (labels .finish))) label
  | .cleanup label => MachineDrainMany.instruction
      (MachineDrainMany.workTapes enumeration (tape 3))
      (fun l => labels (.cleanup l)) (some (labels .finish)) label
  | .finish => .load (fun _ => (initial, none)) .halt

def bodyTapes (tape : Fin 4 → K) (base : K → List Bool) (body : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 0) []) (tape 3) body

def headerTapes (q count : Nat) (tape : Fin 4 → K) (base : K → List Bool)
    (body : List Bool) : K → List Bool :=
  Function.update (bodyTapes tape base body) (tape 3)
    (encodeWords [count, count, q, count] ++ body)

def budget (q count : Nat) (enumeration : Fin stackCount ≃ K) (tape : Fin 4 → K)
    (base : K → List Bool) (body : List Bool) : Nat :=
  body.length + 1 + (6 * (count + 2) + 1) +
    (MachineDrainMany.lengthSum (MachineDrainMany.workTapes enumeration (tape 3))
      (headerTapes q count tape base body) +
      (MachineDrainMany.workTapes enumeration (tape 3)).length) + 1

def finalizeInTime (q : Nat) (enumeration : Fin stackCount ≃ K) (tape : Fin 4 → K)
    (distinct : Function.Injective tape) (initial : A)
    (labels : Labels enumeration (tape 3) → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction q enumeration tape initial labels l)
    (base : K → List Bool) (ambient : A) (register : Option Bool)
    (count : Nat) (body : List Bool)
    (reversed : base (tape 0) = body.reverse)
    (countWord : base (tape 1) = encodeWord count)
    (scratchEmpty : base (tape 2) = []) (outputEmpty : base (tape 3) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .reverse), (ambient, register), base⟩
      (some ⟨none, (initial, none), MachineDrainMany.haltTapes (tape 3)
        (encodeWords [count, count, q, count] ++ body)⟩)
      (budget q count enumeration tape base body) := by
  have different (i j : Fin 4) (h : i ≠ j) : tape i ≠ tape j :=
    fun same => h (distinct same)
  have transferTapes : tapesAt (tape 0) (tape 3) base []
      ((base (tape 0)).reverse.map id ++ base (tape 3)) = bodyTapes tape base body := by
    simp only [reversed, List.reverse_reverse, List.map_id, outputEmpty, List.append_nil]
    rfl
  have transferred : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .reverse), (ambient, register), base⟩
      (some ⟨some (labels (.header TargetHeaderMachine.main)), (ambient, none),
        bodyTapes tape base body⟩) (body.length + 1) := by
    have run := transferAtInTime (Γ := Alphabet (K := K)) (σ := A) (tape 0) (tape 3) (different 0 3 (by decide))
      id false (labels .reverse) (some (labels (.header TargetHeaderMachine.main)))
      program (by simpa only [instruction] using atLabels .reverse) base ambient register
    rw [transferTapes] at run
    simpa only [reversed, List.length_reverse] using run
  have bodyCount : bodyTapes tape base body (headerTape tape 0) = encodeWord count := by
    simp [bodyTapes, headerTape, different 1 3 (by decide), different 1 0 (by decide), countWord]
  have bodyScratch : bodyTapes tape base body (headerTape tape 1) = [] := by
    simp [bodyTapes, headerTape, different 2 3 (by decide), different 2 0 (by decide), scratchEmpty]
  have bodyOutput : bodyTapes tape base body (headerTape tape 2) = body := by
    simp [bodyTapes, headerTape]
  have emitted := TargetHeaderMachine.headerInTime q (headerTape tape)
    (headerTape_injective tape distinct) (fun l => labels (.header l))
    (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration (tape 3))
      (fun l => labels (.cleanup l)) (some (labels .finish)))
    program (fun l => atLabels (.header l)) (bodyTapes tape base body)
    count bodyCount bodyScratch ambient none
  rw [bodyOutput] at emitted
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (labels (.header TargetHeaderMachine.main)), (ambient, none), bodyTapes tape base body⟩
    (some ⟨MachineDrainMany.entry (MachineDrainMany.workTapes enumeration (tape 3))
      (fun l => labels (.cleanup l)) (some (labels .finish)), (ambient, none),
      headerTapes q count tape base body⟩) (6 * (count + 2) + 1) at emitted
  have cleaned := MachineDrainMany.execution
    (MachineDrainMany.workTapes enumeration (tape 3)) (fun l => labels (.cleanup l))
    (some (labels .finish)) program (fun l => atLabels (.cleanup l))
    (headerTapes q count tape base body) ambient none
  rw [MachineDrainMany.finalRegister_none, MachineDrainMany.finalTapes_workTapes] at cleaned
  have headerOutput : headerTapes q count tape base body (tape 3) =
      encodeWords [count, count, q, count] ++ body := by simp [headerTapes]
  rw [headerOutput] at cleaned
  have reset : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .finish), (ambient, none), MachineDrainMany.haltTapes (tape 3)
        (encodeWords [count, count, q, count] ++ body)⟩
      (some ⟨none, (initial, none), MachineDrainMany.haltTapes (tape 3)
        (encodeWords [count, count, q, count] ++ body)⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl 1 }
    change some (TM2.stepAux (program (labels .finish)) _ _) = _
    rw [atLabels]
    rfl
  have first := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ transferred emitted
  have second := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ first cleaned
  have third := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ second reset
  simpa only [budget, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using third

end PerfectCompleteness.TargetFinalizeMachine

end OAI
