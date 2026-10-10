import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineInitialHeaders

namespace OAI

/-! A finite literal setup sequence. Its list is fixed with the machine; no
input word or unbounded address is stored in finite control. -/

namespace UniqueGamesTheorem.Explicit.MachineProductSeed

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer
open UniqueGamesTheorem.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

abbrev Command (K : Type) := K × List Bool
abbrev LocalLabel (_ : Command K) := Unit
abbrev Label (commands : List (Command K)) := MachineFiniteSequence.Label LocalLabel commands

def entry (commands : List (Command K)) (labels : Label commands → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry LocalLabel (fun _ => ()) commands labels exit

def localInstruction (command : Command K) (_ : Unit → Λ) (exit : Option Λ) (_ : Unit) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  pushWord command.1 command.2.reverse (exitAt command.1 exit)

def instruction (commands : List (Command K)) (labels : Label commands → Λ) (exit : Option Λ) :
    Label commands → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  MachineFiniteSequence.instruction LocalLabel (fun _ => ()) localInstruction commands labels exit

def result (command : Command K) (base : K → List Bool) : K → List Bool :=
  Function.update base command.1 (command.2 ++ base command.1)

def finalTapes (commands : List (Command K)) (base : K → List Bool) : K → List Bool :=
  MachineFiniteSequence.resultOf result commands base

@[simp] theorem sequence_steps (commands : List (Command K)) (base : K → List Bool) :
    MachineFiniteSequence.steps result (fun _ _ => 1) commands base = commands.length := by
  induction commands generalizing base with
  | nil => rfl
  | cons command commands ih =>
    simp only [MachineFiniteSequence.steps, ih, List.length_cons]
    omega

/-- Each literal has an actual one-transition trace in the ambient machine. -/
theorem seedTrace (commands : List (Command K)) (labels : Label commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction commands labels exit l)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[commands.length]
      (some ⟨entry commands labels exit, (ambient, register), base⟩) =
      some ⟨exit, (ambient, register), finalTapes commands base⟩ := by
  have h := MachineFiniteSequence.trace LocalLabel (fun _ => ()) localInstruction
    result (fun _ _ => 1) program (fun _ => True) (fun _ => (ambient, register)) id commands
    (by intros; trivial)
    (by
      intro command hc localLabels localExit atLocal tapes ht
      have h := MachineInitialHeaders.literalTrace command.1 command.2.reverse
        (localLabels ()) localExit program (atLocal ()) tapes ambient register
      simpa only [List.reverse_reverse, id_eq, result] using h)
    labels exit atLabels base trivial
  simpa only [sequence_steps, entry, finalTapes, id_eq] using h

theorem finalTapes_frame (commands : List (Command K)) (base : K → List Bool)
    (k : K) (outside : ∀ command ∈ commands, k ≠ command.1) :
    finalTapes commands base k = base k := by
  induction commands generalizing base with
  | nil => rfl
  | cons command commands ih =>
    change finalTapes commands (result command base) k = base k
    rw [ih _ (fun c hc => outside c (by simp [hc]))]
    exact Function.update_of_ne (outside command (by simp)) _ _

theorem finalTapes_field (commands : List (Command K))
    (nodup : (commands.map Prod.fst).Nodup) (base : K → List Bool)
    (command : Command K) (member : command ∈ commands) :
    finalTapes commands base command.1 = command.2 ++ base command.1 := by
  induction commands generalizing base with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at nodup
    rcases List.mem_cons.mp member with rfl | member
    · change finalTapes rest (result command base) command.1 = _
      rw [finalTapes_frame rest _ command.1]
      · simp [result]
      · intro c hc he
        exact nodup.1 (List.mem_map.mpr ⟨c, hc, he.symm⟩)
    · have ne : command.1 ≠ first.1 := by
        intro h
        exact nodup.1 (List.mem_map.mpr ⟨command, member, h⟩)
      change finalTapes rest (result first base) command.1 = _
      rw [ih nodup.2 _ member, result, Function.update_of_ne ne]

end UniqueGamesTheorem.Explicit.MachineProductSeed

end OAI
