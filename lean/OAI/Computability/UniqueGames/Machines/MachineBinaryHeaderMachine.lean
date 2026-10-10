import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI

/-!
An actual finite Boolean-stack routine prepending two unary header words to an
already restored serialized body. It consumes counters containing `n` and `m`
true bits, respectively, in exactly `n + m + 4` transitions. All ambient stacks
and the finite ambient state are preserved. The input counters need no separate
counting pass: a caller can accumulate them while constructing the body.

The generic placement theorem uses only four displayed instruction equations.
The concrete machine below has three Boolean stacks and four control labels;
its final transfer halts directly. This is a staged configuration computation,
not a single-input `initList` assertion that silently assumes two extra inputs.
-/

namespace UniqueGamesTheorem.BinaryHeaderMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

section Placement

variable {K Λ A : Type} [DecidableEq K]

/-- A fixed one-bit push; the finite register is cleared before continuation. -/
def delimiter (destination : K) (next : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push destination (fun _ => false)
    (.load (fun state => (state.1, none)) (.goto fun _ => next))

def tapes (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base variableTape variableCounter)
    clauses clauseCounter) destination output

@[simp] theorem tapes_variables (variableTape clauses destination : K)
    (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output variableTape =
      variableCounter := by
  simp [tapes, vc, vd]

@[simp] theorem tapes_clauses (variableTape clauses destination : K)
    (cd : clauses ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output clauses =
      clauseCounter := by
  simp [tapes, cd]

@[simp] theorem tapes_destination (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output destination =
      output := by
  simp [tapes]

theorem tapes_other (variableTape clauses destination k : K)
    (kv : k ≠ variableTape) (kc : k ≠ clauses) (kd : k ≠ destination)
    (base : K → List Bool) (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output k = base k := by
  simp [tapes, kv, kc, kd]

private theorem update_variables (variableTape clauses destination : K)
    (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      variableTape replacement = tapes variableTape clauses destination base replacement clauseCounter output := by
  funext k
  by_cases hv : k = variableTape
  · subst k
    simp [tapes, vc, vd]
  · by_cases hd : k = destination
    · subst k
      simp [tapes, hv]
    · by_cases hc : k = clauses
      · subst k
        simp [tapes, hv, hd]
      · simp [tapes, hv, hc, hd]

private theorem update_clauses (variableTape clauses destination : K)
    (cd : clauses ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      clauses replacement = tapes variableTape clauses destination base variableCounter replacement output := by
  funext k
  by_cases hc : k = clauses
  · subst k
    simp [tapes, cd]
  · by_cases hd : k = destination
    · subst k
      simp [tapes, hc]
    · simp [tapes, hc, hd]

private theorem update_destination (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      destination replacement = tapes variableTape clauses destination base variableCounter clauseCounter replacement := by
  simp [tapes]

variable (variableTape clauses destination : K)
variable (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (cd : clauses ≠ destination)
variable (clauseStart clauseLoop variableStart variableLoop : Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atClauseStart : program clauseStart = delimiter destination clauseLoop)
variable (atClauseLoop : program clauseLoop =
  loopAt clauses destination id false clauseLoop (some variableStart))
variable (atVariableStart : program variableStart = delimiter destination variableLoop)
variable (atVariableLoop : program variableLoop =
  loopAt variableTape destination id false variableLoop exit)
variable (base : K → List Bool) (ambient : A)

include atClauseStart in
theorem clauseDelimiterStep (variableCounter clauseCounter output : List Bool)
    (register : Option Bool) :
    TM2.step program
      ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base variableCounter clauseCounter output⟩ =
      some ⟨some clauseLoop, (ambient, none),
        tapes variableTape clauses destination base variableCounter clauseCounter (false :: output)⟩ := by
  change some (TM2.stepAux (program clauseStart) _ _) = _
  rw [atClauseStart]
  simp [delimiter, TM2.stepAux, update_destination]

include atVariableStart in
theorem variableDelimiterStep (variableCounter clauseCounter output : List Bool)
    (register : Option Bool) :
    TM2.step program
      ⟨some variableStart, (ambient, register),
        tapes variableTape clauses destination base variableCounter clauseCounter output⟩ =
      some ⟨some variableLoop, (ambient, none),
        tapes variableTape clauses destination base variableCounter clauseCounter (false :: output)⟩ := by
  change some (TM2.stepAux (program variableStart) _ _) = _
  rw [atVariableStart]
  simp [delimiter, TM2.stepAux, update_destination]

include cd atClauseLoop in
theorem clauseCounterTrace (m : Nat) (variableCounter output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[m + 1]
      (some ⟨some clauseLoop, (ambient, register),
        tapes variableTape clauses destination base variableCounter (List.replicate m true) output⟩) =
      some ⟨some variableStart, (ambient, none),
        tapes variableTape clauses destination base variableCounter [] (List.replicate m true ++ output)⟩ := by
  have h := transferAt_fromTapes (Γ := Alphabet) clauses destination cd id false
    clauseLoop (some variableStart) program atClauseLoop
    (tapes variableTape clauses destination base variableCounter (List.replicate m true) output)
    ambient register
  change (nextAt destination program)^[m + 1]
    (some ⟨some clauseLoop, (ambient, register),
      tapes variableTape clauses destination base variableCounter (List.replicate m true) output⟩) = _
  simpa only [tapes_clauses variableTape clauses destination cd, tapes_destination,
    List.length_replicate, List.reverse_replicate, List.map_id_fun, id_eq,
    tapesAt, update_clauses variableTape clauses destination cd, update_destination,
    nextAt, advance] using h

include vc vd atVariableLoop in
theorem variableCounterTrace (n : Nat) (clauseCounter output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[n + 1]
      (some ⟨some variableLoop, (ambient, register),
        tapes variableTape clauses destination base (List.replicate n true) clauseCounter output⟩) =
      some ⟨exit, (ambient, none),
        tapes variableTape clauses destination base [] clauseCounter (List.replicate n true ++ output)⟩ := by
  have h := transferAt_fromTapes (Γ := Alphabet) variableTape destination vd id false
    variableLoop exit program atVariableLoop
    (tapes variableTape clauses destination base (List.replicate n true) clauseCounter output)
    ambient register
  change (nextAt destination program)^[n + 1]
    (some ⟨some variableLoop, (ambient, register),
      tapes variableTape clauses destination base (List.replicate n true) clauseCounter output⟩) = _
  simpa only [tapes_variables variableTape clauses destination vc vd, tapes_destination,
    List.length_replicate, List.reverse_replicate, List.map_id_fun, id_eq,
    tapesAt, update_variables variableTape clauses destination vc vd, update_destination,
    nextAt, advance] using h

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

include vc vd cd atClauseStart atClauseLoop atVariableStart atVariableLoop

/-- The actual four-phase routine, with exact unary header and preserved body. -/
theorem headerTrace (n m : Nat) (body : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[n + m + 4]
      (some ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base
          (List.replicate n true) (List.replicate m true) body⟩) =
      some ⟨exit, (ambient, none),
        tapes variableTape clauses destination base [] [] (encodeWord n ++ encodeWord m ++ body)⟩ := by
  have first := clauseDelimiterStep variableTape clauses destination clauseStart clauseLoop program
    atClauseStart base ambient (List.replicate n true) (List.replicate m true) body register
  change (advance (TM2.step program))^[1]
    (some ⟨some clauseStart, (ambient, register),
      tapes variableTape clauses destination base (List.replicate n true) (List.replicate m true) body⟩) = _ at first
  have second := clauseCounterTrace variableTape clauses destination cd clauseLoop variableStart program
    atClauseLoop base ambient m (List.replicate n true) (false :: body) none
  have third := variableDelimiterStep variableTape clauses destination variableStart variableLoop program
    atVariableStart base ambient (List.replicate n true) []
    (List.replicate m true ++ false :: body) none
  change (advance (TM2.step program))^[1]
    (some ⟨some variableStart, (ambient, none),
      tapes variableTape clauses destination base (List.replicate n true) []
        (List.replicate m true ++ false :: body)⟩) = _ at third
  have fourth := variableCounterTrace variableTape clauses destination vc vd variableLoop exit program
    atVariableLoop base ambient n [] (false :: (List.replicate m true ++ false :: body)) none
  have full := joinTrace (joinTrace (joinTrace first second) third) fourth
  have htime : ((1 + (m + 1)) + 1) + (n + 1) = n + m + 4 := by omega
  rw [htime] at full
  simpa only [encodeWord, List.append_assoc, List.singleton_append,
    List.cons_append, List.nil_append] using full

def headerInTime (n m : Nat) (body : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base (List.replicate n true) (List.replicate m true) body⟩
      (some ⟨exit, (ambient, none),
        tapes variableTape clauses destination base [] [] (encodeWord n ++ encodeWord m ++ body)⟩)
      (n + m + 4) where
  steps := n + m + 4
  evals_in_steps := headerTrace variableTape clauses destination vc vd cd
    clauseStart clauseLoop variableStart variableLoop exit program
    atClauseStart atClauseLoop atVariableStart atVariableLoop base ambient n m body register
  steps_le_m := Nat.le_refl _

end Placement

abbrev ConcreteTape := Fin 3
abbrev ConcreteLabel := Fin 4

def concreteProgram (label : ConcreteLabel) :
    TM2.Stmt (Alphabet (K := ConcreteTape)) ConcreteLabel (State Unit) :=
  if label = 0 then delimiter 2 1
  else if label = 1 then loopAt 1 2 id false 1 (some 2)
  else if label = 2 then delimiter 2 3
  else loopAt 0 2 id false 3 none

abbrev machine : FinTM2 where
  K := ConcreteTape
  k₀ := 0
  k₁ := 2
  Γ := Alphabet
  Λ := ConcreteLabel
  main := 0
  σ := State Unit
  initialState := ((), none)
  m := concreteProgram

/-- Concrete entry configuration carries two physical counters and the body. -/
def start (n m : Nat) (body : List Bool) : machine.Cfg :=
  ⟨some 0, ((), none),
    tapes 0 1 2 (fun _ : ConcreteTape => []) (List.replicate n true) (List.replicate m true) body⟩

theorem haltList_eq (body : List Bool) :
    haltList machine body =
      ⟨none, ((), none), tapes 0 1 2 (fun _ : ConcreteTape => []) [] [] body⟩ := by
  unfold haltList
  congr 1
  funext k
  fin_cases k <;> simp [machine, tapes]

/-- Genuine staged execution of the concrete four-label finite machine. -/
def machineInTime (n m : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime machine.step (start n m body)
      (some (haltList machine (encodeWord n ++ encodeWord m ++ body))) (n + m + 4) := by
  rw [haltList_eq]
  exact headerInTime (0 : ConcreteTape) 1 2 (by decide) (by decide) (by decide)
    (0 : ConcreteLabel) 1 2 3 none concreteProgram
    (by simp [concreteProgram]) (by simp [concreteProgram])
    (by simp [concreteProgram]) (by simp [concreteProgram])
    (fun _ => []) () n m body none

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end UniqueGamesTheorem.BinaryHeaderMachine

end OAI
