import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineDrain
import OAI.Combinatorics.IndependentSets.Machines.MachineFiniteSequence

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev Tapes (K : Type) := K → List Bool
abbrev LocalLabel (_ : K) := Unit
abbrev Label (chosen : List K) := MachineFiniteSequence.Label (LocalLabel (K := K)) chosen
abbrev Data (K : Type) := Tapes K × Option Bool

def entry (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel (K := K)) (fun _ => ()) chosen labels exit

def localInstruction (source : K) (labels : Unit → Λ) (exit : Option Λ) (_ : Unit) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineDrain.drain source (labels ()) exit

def instruction (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) :
    Label chosen → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineFiniteSequence.instruction (LocalLabel (K := K)) (fun _ => ())
    localInstruction chosen labels exit

def result (source : K) (data : Data K) : Data K :=
  (Function.update data.1 source [], none)

def cost (source : K) (data : Data K) : Nat := (data.1 source).length + 1

def finalTapes : List K → Tapes K → Tapes K
  | [], base => base
  | source :: chosen, base => finalTapes chosen (Function.update base source [])

def finalRegister : List K → Option Bool → Option Bool
  | [], register => register
  | _ :: _, _ => none

omit [DecidableEq K] in
@[simp] theorem finalRegister_none (chosen : List K) : finalRegister chosen none = none := by
  cases chosen <;> rfl

def steps : List K → Tapes K → Nat
  | [], _ => 0
  | source :: chosen, base => (base source).length + 1 +
      steps chosen (Function.update base source [])

@[simp] theorem sequence_result (chosen : List K) (base : Tapes K) (register : Option Bool) :
    MachineFiniteSequence.resultOf result chosen (base, register) =
      (finalTapes chosen base, finalRegister chosen register) := by
  induction chosen generalizing base register with
  | nil => rfl
  | cons source chosen ih =>
      change MachineFiniteSequence.resultOf result chosen (Function.update base source [], none) =
        (finalTapes chosen (Function.update base source []), none)
      rw [ih, finalRegister_none]

@[simp] theorem sequence_steps (chosen : List K) (base : Tapes K) (register : Option Bool) :
    MachineFiniteSequence.steps result cost chosen (base, register) = steps chosen base := by
  induction chosen generalizing base register with
  | nil => rfl
  | cons source chosen ih =>
      simp only [MachineFiniteSequence.steps, result, cost, steps, ih]

theorem finalTapes_apply (chosen : List K) (base : Tapes K) (k : K) :
    finalTapes chosen base k = if k ∈ chosen then [] else base k := by
  induction chosen generalizing base with
  | nil => simp [finalTapes]
  | cons source chosen ih =>
      rw [finalTapes, ih]
      by_cases h : k = source
      · subst k
        simp
      · simp [List.mem_cons, h]

theorem finalTapes_mem (chosen : List K) (base : Tapes K) (k : K) (h : k ∈ chosen) :
    finalTapes chosen base k = [] := by rw [finalTapes_apply, ite_eq_left h]

theorem finalTapes_not_mem (chosen : List K) (base : Tapes K) (k : K) (h : k ∉ chosen) :
    finalTapes chosen base k = base k := by rw [finalTapes_apply, ite_eq_right h]

def lengthSum (chosen : List K) (base : Tapes K) : Nat :=
  (chosen.map (fun k => (base k).length)).sum

omit [DecidableEq K] in
theorem lengthSum_mono (chosen : List K) (first second : Tapes K)
    (h : ∀ k, (first k).length ≤ (second k).length) :
    lengthSum chosen first ≤ lengthSum chosen second := by
  induction chosen with
  | nil => exact Nat.le_refl 0
  | cons source chosen ih =>
      simp only [lengthSum, List.map_cons, List.sum_cons] at ih ⊢
      exact Nat.add_le_add (h source) ih

theorem steps_le (chosen : List K) (base : Tapes K) :
    steps chosen base ≤ lengthSum chosen base + chosen.length := by
  induction chosen generalizing base with
  | nil => simp [steps, lengthSum]
  | cons source chosen ih =>
      have hshort : ∀ k, ((Function.update base source []) k).length ≤ (base k).length := by
        intro k
        by_cases h : k = source
        · subst k
          simp
        · simp [Function.update_of_ne h]
      have hsum := lengthSum_mono chosen (Function.update base source []) base hshort
      have htail := ih (Function.update base source [])
      simp only [steps, lengthSum, List.map_cons, List.sum_cons, List.length_cons] at hsum htail ⊢
      omega

theorem steps_le_uniform (chosen : List K) (base : Tapes K) (bound : Nat)
    (h : ∀ k, (base k).length ≤ bound) :
    steps chosen base ≤ chosen.length * (bound + 1) := by
  have hsum : lengthSum chosen base ≤ chosen.length * bound := by
    induction chosen with
    | nil => simp [lengthSum]
    | cons source chosen ih =>
        simp only [lengthSum, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
          Nat.one_mul] at ih ⊢
        have hs := h source
        omega
  have hc := steps_le chosen base
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem trace (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction chosen labels exit l)
    (base : Tapes K) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps chosen base]
      (some ⟨entry chosen labels exit, (ambient, register), base⟩) =
    some ⟨exit, (ambient, finalRegister chosen register), finalTapes chosen base⟩ := by
  have run := MachineFiniteSequence.trace
    (LocalLabel := LocalLabel (K := K)) (main := fun _ => ())
    (localInstruction := localInstruction (σ := σ)) (result := result) (cost := cost)
    program (fun _ : Data K => True) (fun data => (ambient, data.2)) (fun data => data.1)
    chosen (by intros; trivial)
    (by
      intro source _ localLabels localExit atLocal data _
      rcases data with ⟨tapes, reg⟩
      simpa only [cost, result, Function.update_eq_self] using
        MachineDrain.drainTrace source (localLabels ()) localExit program (atLocal ())
          tapes (tapes source) ambient reg)
    labels exit atLabels (base, register) trivial
  simpa only [sequence_steps, sequence_result, entry] using run

def execution (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction chosen labels exit l)
    (base : Tapes K) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry chosen labels exit, (ambient, register), base⟩
      (some ⟨exit, (ambient, finalRegister chosen register), finalTapes chosen base⟩)
      (lengthSum chosen base + chosen.length) where
  steps := steps chosen base
  evals_in_steps := trace chosen labels exit program atLabels base ambient register
  steps_le_m := steps_le chosen base

def workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K) : List K :=
  (List.ofFn (fun i => enumeration i)).filter (fun k => decide (k ≠ output))

@[simp] theorem mem_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output k : K) :
    k ∈ workTapes enumeration output ↔ k ≠ output := by
  have hmem : k ∈ List.ofFn (fun i => enumeration i) := by
    apply List.mem_ofFn.mpr
    exact ⟨enumeration.symm k, enumeration.apply_symm_apply k⟩
  simp [workTapes, hmem]

theorem workTapes_length_le {N : Nat} (enumeration : Fin N ≃ K) (output : K) :
    (workTapes enumeration output).length ≤ N := by
  simpa only [workTapes, List.length_ofFn] using
    List.length_filter_le (fun k => decide (k ≠ output)) (List.ofFn (fun i => enumeration i))

def haltTapes (output : K) (word : List Bool) : Tapes K :=
  fun k => if k = output then word else []

theorem finalTapes_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K)
    (base : Tapes K) :
    finalTapes (workTapes enumeration output) base = haltTapes output (base output) := by
  funext k
  rw [finalTapes_apply]
  by_cases h : k = output
  · subst k
    simp [haltTapes]
  · simp [haltTapes, h]

theorem cleanupTrace {N : Nat} (enumeration : Fin N ≃ K) (output : K)
    (labels : Label (workTapes enumeration output) → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) =
      instruction (workTapes enumeration output) labels none l)
    (base : Tapes K) (ambient : σ) :
    (advance (TM2.step program))^[steps (workTapes enumeration output) base]
      (some ⟨entry (workTapes enumeration output) labels none, (ambient, none), base⟩) =
    some ⟨none, (ambient, none), haltTapes output (base output)⟩ := by
  simpa only [finalRegister_none, finalTapes_workTapes] using
    trace (workTapes enumeration output) labels none program atLabels base ambient none

end IndependentSetsGames.Foundations.Complexity.MachineDrainMany

end OAI
