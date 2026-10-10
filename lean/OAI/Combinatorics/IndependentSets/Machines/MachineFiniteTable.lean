import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.Machine
import OAI.Combinatorics.IndependentSets.PCP.GraphIterationBounds
import OAI.Combinatorics.IndependentSets.Machines.MachineInitialHeaders

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineFiniteTable

open Turing
open IndependentSetsGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K] [DecidableEq σ]
variable {Γ : K → Type}

def dispatch (dst : K) (table : σ → List (Γ dst))
    (next : TM2.Stmt Γ Λ σ) : List σ → TM2.Stmt Γ Λ σ
  | [] => next
  | key :: rest =>
      .branch (fun state => decide (state = key))
        (pushWord dst (table key).reverse next) (dispatch dst table next rest)

theorem stepAux_dispatch (dst : K) (table : σ → List (Γ dst))
    (next : TM2.Stmt Γ Λ σ) (keys : List σ) (state : σ)
    (hstate : state ∈ keys) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (dispatch dst table next keys) state tapes =
      TM2.stepAux next state (Function.update tapes dst (table state ++ tapes dst)) := by
  induction keys with
  | nil => simp at hstate
  | cons key rest ih =>
      by_cases h : state = key
      · subst state
        simp only [dispatch, TM2.stepAux, decide_true, Bool.cond_true]
        simpa only [List.reverse_reverse] using
          stepAux_pushWord dst (table key).reverse next key tapes
      · have hm : state ∈ rest := (List.mem_cons.mp hstate).resolve_left h
        simpa only [dispatch, TM2.stepAux, h, decide_false, Bool.cond_false] using ih hm

omit [DecidableEq K] in

theorem dispatch_push_bound (dst : K) (table : σ → List (Γ dst))
    (next : TM2.Stmt Γ Λ σ) (keys : List σ) :
    Runtime.statementPushBound (dispatch dst table next keys) ≤
      (keys.map (fun state => (table state).length)).sum +
        Runtime.statementPushBound next := by
  induction keys with
  | nil => simp [dispatch]
  | cons key rest ih =>
      simp only [dispatch, Runtime.statementPushBound, statementPushBound_pushWord,
        List.length_reverse, List.map_cons, List.sum_cons]
      apply max_le <;> omega

def emit (dst : K) (table : σ → List (Γ dst)) (keys : List σ)
    (next : TM2.Stmt Γ Λ σ) : TM2.Stmt Γ Λ σ :=
  dispatch dst table next keys

def tableBound (dst : K) (table : σ → List (Γ dst)) (keys : List σ) : ℕ :=
  (keys.map (fun state => (table state).length)).sum

theorem stepAux_emit (dst : K) (table : σ → List (Γ dst))
    (keys : List σ) (hkeys : ∀ state, state ∈ keys) (next : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (emit dst table keys next) state tapes =
      TM2.stepAux next state (Function.update tapes dst (table state ++ tapes dst)) :=
  stepAux_dispatch dst table next keys state (hkeys state) tapes

omit [DecidableEq K] in
theorem emit_push_bound (dst : K) (table : σ → List (Γ dst))
    (keys : List σ) (next : TM2.Stmt Γ Λ σ) :
    Runtime.statementPushBound (emit dst table keys next) ≤
      tableBound dst table keys + Runtime.statementPushBound next :=
  dispatch_push_bound dst table next _

def emitInTime (dst : K) (table : σ → List (Γ dst))
    (keys : List σ) (hkeys : ∀ state, state ∈ keys)
    (program : Λ → TM2.Stmt Γ Λ σ) (label exitLabel : Λ)
    (atLabel : program label = emit dst table keys (.goto (fun _ => exitLabel)))
    (state : σ) (tapes : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some label, state, tapes⟩
      (some ⟨some exitLabel, state,
        Function.update tapes dst (table state ++ tapes dst)⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program label) state tapes) = _
    rw [atLabel, stepAux_emit dst table keys hkeys]
    rfl
  steps_le_m := Nat.le_refl _

omit [DecidableEq σ] in
theorem output_frame (dst : K) (table : σ → List (Γ dst))
    (state : σ) (tapes : ∀ k, List (Γ k)) (k : K) (h : k ≠ dst) :
    (Function.update tapes dst (table state ++ tapes dst)) k = tapes k := by
  simp [Function.update, h]

end IndependentSetsGames.Foundations.Complexity.MachineFiniteTable

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineModel

open Turing Complexity Hastad

inductive Tape
  | input | «variables» | counter | index | field (slot : Fin 6)
  | scratch | reversed | output
  deriving DecidableEq

deriving instance Fintype for Tape

abbrev Signs := Bool × Bool × Bool
abbrev State := Signs × Option Bool
abbrev Alphabet (_ : Tape) := Bool

inductive CopyPhase
  | tailVariables (slot : Fin 3)
  | tailIndex (slot : Fin 3)
  | variableName (slot : Fin 3)
  | reverseIndex (slot : Fin 3) (orientation : Bool)
  | dummyVariables | dummyIndex | dummyReverse
  deriving DecidableEq

deriving instance Fintype for CopyPhase

inductive Label
  | headerStart (slot : Fin 2) | headerLoop (slot : Fin 2)
  | scanN | restoreN | scanM1 | restoreM1 | closeFirst
  | scanM6 | restoreM6 | closeSecond | initializeIndex | guard
  | fieldStart (slot : Fin 6) | fieldLoop (slot : Fin 6) | loadSigns
  | scan (phase : CopyPhase) | restore (phase : CopyPhase)
  | closeTail (slot : Fin 3) (orientation : Bool)
  | closeReverse (slot : Fin 3) (orientation : Bool)
  | relation (slot : Fin 3) (orientation : Bool)
  | cleanupField (slot : Fin 6) | incrementIndex
  | closeDummyTail | closeDummyReverse | dummyRelation
  | cleanupFinal (slot : Fin 3) | reset | finalReverse
  deriving DecidableEq

deriving instance Fintype for Label

def initialState : State := ((false, false, false), none)

def stateKeys : List State :=
  [false, true].flatMap fun a => [false, true].flatMap fun b =>
    [false, true].flatMap fun c =>
      [none, some false, some true].map fun register => ((a, b, c), register)

theorem stateKeys_complete (state : State) : state ∈ stateKeys := by
  rcases state with ⟨⟨a, b, c⟩, register⟩
  cases a <;> cases b <;> cases c <;> cases register with
  | none => simp [stateKeys]
  | some bit => cases bit <;> simp [stateKeys]

def nameField (slot : Fin 3) : Fin 6 := ⟨2 * slot.val, by omega⟩

def copySource : CopyPhase → Tape
  | .tailVariables _ | .dummyVariables => .«variables»
  | .variableName slot => .field (nameField slot)
  | _ => .index

def copyScale : CopyPhase → Nat
  | .reverseIndex _ _ | .dummyReverse => 6
  | _ => 1

def copyNext : CopyPhase → Label
  | .tailVariables slot => .scan (.tailIndex slot)
  | .tailIndex slot => .closeTail slot false
  | .variableName slot => .closeTail slot true
  | .reverseIndex slot orientation => .closeReverse slot orientation
  | .dummyVariables => .scan .dummyIndex
  | .dummyIndex => .closeDummyTail
  | .dummyReverse => .closeDummyReverse

def relationNext (slot : Fin 3) (orientation : Bool) : Label :=
  if orientation then
    if h : slot.val + 1 < 3 then .scan (.tailVariables ⟨slot.val + 1, h⟩)
    else .cleanupField 0
  else .scan (.variableName slot)

def finalTape (slot : Fin 3) : Tape :=
  if slot.val = 0 then .«variables» else if slot.val = 1 then .counter else .index

def drain (tape : Tape) (again next : Label) : TM2.Stmt Alphabet Label State :=
  MachineDrain.drain tape again (some next)

def headerTape (slot : Fin 2) : Tape := if slot.val = 0 then .«variables» else .counter

def relationOutput (slot : Fin 3) (orientation : Bool) (state : State) : List Bool :=
  (encodeWords (RawInitialRows.relationWordsFor state.1
    (RawInitialTables.slotOrder.symm slot) orientation)).reverse

def program : Label → TM2.Stmt Alphabet Label State
  | .headerStart slot => SourceMachine.fieldStart (headerTape slot) (.headerLoop slot)
  | .headerLoop slot => SourceMachine.fieldLoop .input (headerTape slot) (.headerLoop slot)
      (if slot.val = 0 then some (.headerStart 1) else some .scanN)
  | .scanN => MachineInitialHeaders.prefixScan .«variables» .scratch .reversed 1 .scanN .restoreN
  | .restoreN => Reduction.MachineTransfer.loopAt .scratch .«variables» id false .restoreN (some .scanM1)
  | .scanM1 => MachineInitialHeaders.prefixScan .counter .scratch .reversed 1 .scanM1 .restoreM1
  | .restoreM1 => Reduction.MachineTransfer.loopAt .scratch .counter id false .restoreM1 (some .closeFirst)
  | .closeFirst => Reduction.MachineSubstitution.pushWord .reversed [true, false]
      (.goto fun _ => .scanM6)
  | .scanM6 => MachineInitialHeaders.prefixScan .counter .scratch .reversed 6 .scanM6 .restoreM6
  | .restoreM6 => Reduction.MachineTransfer.loopAt .scratch .counter id false .restoreM6 (some .closeSecond)
  | .closeSecond => Reduction.MachineSubstitution.pushWord .reversed [true, false]
      (.goto fun _ => .initializeIndex)
  | .initializeIndex => .push .index (fun _ => false) (.goto fun _ => .guard)
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) (.scan .dummyVariables)
  | .fieldStart slot => SourceMachine.fieldStart (.field slot) (.fieldLoop slot)
  | .fieldLoop slot => SourceMachine.fieldLoop .input (.field slot) (.fieldLoop slot)
      (if h : slot.val + 1 < 6 then some (.fieldStart ⟨slot.val + 1, h⟩)
        else some .loadSigns)
  | .loadSigns =>
      .peek (.field 1) (fun state head => ((head.getD false, state.1.2), state.2))
        (.peek (.field 3) (fun state head => ((state.1.1, head.getD false, state.1.2.2), state.2))
          (.peek (.field 5) (fun state head => ((state.1.1, state.1.2.1, head.getD false), state.2))
            (.load (fun state => (state.1, none)) (.goto fun _ => .scan (.tailVariables 0)))))
  | .scan phase => MachineInitialHeaders.prefixScan (copySource phase) .scratch .reversed
      (copyScale phase) (.scan phase) (.restore phase)
  | .restore phase => Reduction.MachineTransfer.loopAt .scratch (copySource phase) id false
      (.restore phase) (some (copyNext phase))
  | .closeTail slot orientation => .push .reversed (fun _ => false)
      (.goto fun _ => .scan (.reverseIndex slot orientation))
  | .closeReverse slot orientation => Reduction.MachineSubstitution.pushWord .reversed
      (encodeWord (2 * slot.val + if orientation then 0 else 1))
        (.goto fun _ => .relation slot orientation)
  | .relation slot orientation => MachineFiniteTable.emit .reversed
      (relationOutput slot orientation)
      stateKeys (.goto fun _ => relationNext slot orientation)
  | .cleanupField slot => drain (.field slot) (.cleanupField slot)
      (if h : slot.val + 1 < 6 then .cleanupField ⟨slot.val + 1, h⟩ else .incrementIndex)
  | .incrementIndex => .push .index (fun _ => true) (.goto fun _ => .guard)
  | .closeDummyTail => .push .reversed (fun _ => false) (.goto fun _ => .scan .dummyReverse)
  | .closeDummyReverse => .push .reversed (fun _ => false) (.goto fun _ => .dummyRelation)
  | .dummyRelation => Reduction.MachineSubstitution.pushWord .reversed
      (encodeWords (GraphTables.relationWords (GraphTables.relationOf (fun _ _ => true))))
        (.goto fun _ => .cleanupFinal 0)
  | .cleanupFinal slot => drain (finalTape slot) (.cleanupFinal slot)
      (if h : slot.val + 1 < 3 then .cleanupFinal ⟨slot.val + 1, h⟩ else .reset)
  | .reset => .load (fun _ => initialState) (.goto fun _ => .finalReverse)
  | .finalReverse => Reduction.MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program

end IndependentSetsGames.Foundations.PCP.RawInitialMachineModel

end OAI
