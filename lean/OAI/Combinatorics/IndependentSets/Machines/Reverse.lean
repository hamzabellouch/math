import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineExpanderRowLookup

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineExpanderRow

section
open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineComposition
variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

variable {d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool)
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code

theorem reversePhaseTrace :
    (advance (TM2.step target))^[(base (ports .queryReverse)).length + 1]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          ((base (ports .queryReverse)).reverse ++ base (ports .queryIndex))⟩ := by
  have h := Reduction.MachineTransfer.transferAt_fromTapes
    (ports .queryReverse) (ports .queryIndex)
    (fun h => (by decide : Tape.queryReverse ≠ .queryIndex) (distinct h))
    id false (labels (reversePhaseLabel second))
    (some (labels (lookupPhaseLabel second (.run .copyFirst)))) target
    (by cases second <;> exact code _) base ambient register
  unfold Reduction.MachineTransfer.nextAt at h
  unfold advance
  simpa only [List.map_id] using h

def reversePhaseInTime :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩
      (some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          ((base (ports .queryReverse)).reverse ++ base (ports .queryIndex))⟩)
      ((base (ports .queryReverse)).length + 1) where
  steps := (base (ports .queryReverse)).length + 1
  evals_in_steps := reversePhaseTrace second positive H ports distinct labels exit target code
    base ambient register
  steps_le_m := Nat.le_refl _

theorem reversePhaseTrace_unary (index : Nat) (suffix : List Bool)
    (queryWord : base (ports .queryReverse) = (encodeWord index).reverse)
    (indexWord : base (ports .queryIndex) = suffix) :
    (advance (TM2.step target))^[index + 2]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          (encodeWord index ++ suffix)⟩ := by
  have h := reversePhaseTrace second positive H ports distinct labels exit target code
    base ambient register
  simpa only [queryWord, indexWord, List.length_reverse, encodeWord_length,
    List.reverse_reverse, Nat.add_assoc] using h

end

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

@[simp] private theorem dirtyTape_zero : dirtyTape 0 = .queryIndex := rfl
@[simp] private theorem dirtyTape_one : dirtyTape 1 = .lookupOutput := rfl
@[simp] private theorem dirtyTape_two : dirtyTape 2 = .quotientFirst := rfl
@[simp] private theorem dirtyTape_three : dirtyTape 3 = .quotientSecond := rfl
@[simp] private theorem dirtyTape_four : dirtyTape 4 = .remainderFirst := rfl
@[simp] private theorem dirtyTape_five : dirtyTape 5 = .remainderSecond := rfl

variable {K Λ ρ : Type} [DecidableEq K]

def cleanupTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update base (ports .queryIndex) [])
            (ports .lookupOutput) [])
          (ports .quotientFirst) [])
        (ports .quotientSecond) [])
      (ports .remainderFirst) [])
    (ports .remainderSecond) []

def cleanupSteps (ports : Tape → K) (base : K → List Bool) : Nat :=
  ((base (ports .queryIndex)).length + 1) +
  ((base (ports .lookupOutput)).length + 1) +
  ((base (ports .quotientFirst)).length + 1) +
  ((base (ports .quotientSecond)).length + 1) +
  ((base (ports .remainderFirst)).length + 1) +
  ((base (ports .remainderSecond)).length + 1)

omit [DecidableEq K] in
theorem cleanupSteps_eq_sum (ports : Tape → K) (base : K → List Bool) :
    cleanupSteps ports base = ∑ i : Fin 6, ((base (ports (dirtyTape i))).length + 1) := by
  simp [cleanupSteps, Fin.sum_univ_succ, Nat.add_assoc]

@[simp] theorem cleanupTapes_dirty (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (i : Fin 6) :
    cleanupTapes ports base (ports (dirtyTape i)) = [] := by
  fin_cases i <;>
    simp [cleanupTapes, distinct.eq_iff]

theorem cleanupTapes_other (ports : Tape → K) (base : K → List Bool) (k : K)
    (outside : ∀ i : Fin 6, k ≠ ports (dirtyTape i)) :
    cleanupTapes ports base k = base k := by
  have h0 := outside 0
  have h1 := outside 1
  have h2 := outside 2
  have h3 := outside 3
  have h4 := outside 4
  have h5 := outside 5
  change k ≠ ports .queryIndex at h0
  change k ≠ ports .lookupOutput at h1
  change k ≠ ports .quotientFirst at h2
  change k ≠ ports .quotientSecond at h3
  change k ≠ ports .remainderFirst at h4
  change k ≠ ports .remainderSecond at h5
  simp [cleanupTapes, h0, h1, h2, h3, h4, h5]

@[simp] theorem cleanupTapes_table (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) :
    cleanupTapes ports base (ports .table) = base (ports .table) := by
  simp [cleanupTapes, distinct.eq_iff]

@[simp] theorem cleanupTapes_inputVertex (ports : Tape → K)
    (distinct : Function.Injective ports) (base : K → List Bool) :
    cleanupTapes ports base (ports .inputVertex) = base (ports .inputVertex) := by
  simp [cleanupTapes, distinct.eq_iff]

@[simp] theorem cleanupTapes_output (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) :
    cleanupTapes ports base (ports .output) = base (ports .output) := by
  simp [cleanupTapes, distinct.eq_iff]

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

variable [Fintype ρ] {d : Nat}

theorem cleanupOneTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (i : Fin 6) (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[((base (ports (dirtyTape i))).length + 1)]
      (some ⟨some (labels (.cleanup i)), state, base⟩) =
      some ⟨some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩)
          else labels .done),
        (state.1, none), Function.update base (ports (dirtyTape i)) []⟩ := by
  have run := MachineDrain.drainTrace (ports (dirtyTape i)) (labels (.cleanup i))
    (some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩)
      else labels .done)) target
    (by simpa only [statement] using code (.cleanup i))
    base (base (ports (dirtyTape i))) state.1 state.2
  simpa only [Function.update_eq_self] using run

theorem cleanupTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[cleanupSteps ports base]
      (some ⟨some (labels (.cleanup 0)), state, base⟩) =
      some ⟨some (labels .done), (state.1, none), cleanupTapes ports base⟩ := by
  let t1 := Function.update base (ports .queryIndex) []
  let t2 := Function.update t1 (ports .lookupOutput) []
  let t3 := Function.update t2 (ports .quotientFirst) []
  let t4 := Function.update t3 (ports .quotientSecond) []
  let t5 := Function.update t4 (ports .remainderFirst) []
  have h0 := cleanupOneTraceAt positive H ports labels exit target code 0 base state
  have h1 := cleanupOneTraceAt positive H ports labels exit target code 1 t1 (state.1, none)
  have h2 := cleanupOneTraceAt positive H ports labels exit target code 2 t2 (state.1, none)
  have h3 := cleanupOneTraceAt positive H ports labels exit target code 3 t3 (state.1, none)
  have h4 := cleanupOneTraceAt positive H ports labels exit target code 4 t4 (state.1, none)
  have h5 := cleanupOneTraceAt positive H ports labels exit target code 5 t5 (state.1, none)
  simp [t1, t2, t3, t4, t5, distinct.eq_iff,
    -Function.iterate_succ] at h0 h1 h2 h3 h4 h5
  have finished := join_trace (join_trace (join_trace (join_trace (join_trace h0 h1) h2) h3) h4) h5
  simpa only [cleanupSteps, cleanupTapes] using finished

theorem doneStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .done), state, base⟩ = some ⟨exit, state, base⟩ := by
  change some (TM2.stepAux (target (labels .done)) state base) = _
  rw [code]
  cases exit <;> rfl

theorem cleanupExitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[cleanupSteps ports base + 1]
      (some ⟨some (labels (.cleanup 0)), state, base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes ports base⟩ := by
  have cleaned := cleanupTraceAt positive H ports distinct labels exit target code base state
  have done : (advance (TM2.step target))^[1]
      (some ⟨some (labels .done), (state.1, none), cleanupTapes ports base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes ports base⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      doneStepAt positive H ports labels exit target code (cleanupTapes ports base) (state.1, none)
  exact join_trace cleaned done

def initializedTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update base (ports .quotientFirst) (false :: base (ports .quotientFirst)))
        (ports .quotientSecond) (false :: base (ports .quotientSecond)))
      (ports .remainderFirst) (false :: base (ports .remainderFirst)))
    (ports .remainderSecond) (false :: base (ports .remainderSecond))

theorem initializeStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .initialize), state, base⟩ =
      some ⟨some (labels (.firstEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        (state.1, none), initializedTapes ports base⟩ := by
  change some (TM2.stepAux (target (labels .initialize)) state base) = _
  rw [code]
  simp [statement, TM2.stepAux, initializedTapes, distinct.eq_iff]

def clearedQueryTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update base (ports .queryIndex) (base (ports .queryIndex)).tail)
    (ports .lookupOutput) (base (ports .lookupOutput)).tail

theorem clearQueryStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .clearQuery), state, base⟩ =
      some ⟨some (labels (.secondEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        state, clearedQueryTapes ports base⟩ := by
  change some (TM2.stepAux (target (labels .clearQuery)) state base) = _
  rw [code]
  simp [statement, TM2.stepAux, clearedQueryTapes, distinct.eq_iff]

end IndependentSetsGames.Foundations.Complexity.MachineExpanderRow

end OAI
