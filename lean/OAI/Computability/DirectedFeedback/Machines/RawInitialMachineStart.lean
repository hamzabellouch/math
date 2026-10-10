import Mathlib
import OAI.Computability.DirectedFeedback.Machines.GraphCounterFinish

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.PCP.RawInitialMachineStart

open Turing Complexity Hastad RawInitialMachineModel

def inputTapes (bits : List Bool) : Tape → List Bool
  | .input => bits
  | _ => []

private def firstTapes_inline_RawInitialMachineStart (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => encodeWord m ++ clauseBits
  | .«variables» => encodeWord n
  | _ => []

def counterTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .«variables» => encodeWord n
  | .counter => encodeWord m
  | _ => []

private def headerTapes_inline_RawInitialMachineStart (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .«variables» => encodeWord n
  | .counter => encodeWord m
  | .reversed => (encodeWords [n + m + 1, 6 * m + 1]).reverse
  | _ => []

def startTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .«variables» => encodeWord n
  | .counter => encodeWord m
  | .index => [false]
  | .reversed => (encodeWords [n + m + 1, 6 * m + 1]).reverse
  | _ => []

theorem initList_eq (bits : List Bool) :
    initList machine bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1
  funext k
  change Tape at k
  cases k <;> rfl

private theorem trace_trans_inline_RawInitialMachineStart {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem readCountersTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[n + m + 4]
      (some (initList machine (encodeWords [n, m] ++ clauseBits))) =
      some ⟨some .scanN, initialState, counterTapes n m clauseBits⟩ := by
  let t0 := inputTapes (encodeWords [n, m] ++ clauseBits)
  have first := (SourceMachine.fieldInTime .input .«variables» (by decide)
    (.headerStart 0) (.headerLoop 0) (some (.headerStart 1)) program rfl rfl
    t0 n (encodeWord m ++ clauseBits)
    (by simp [t0, inputTapes, encodeWords, List.append_assoc])
    (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[n + 2]
    (some ⟨some (.headerStart 0), initialState, t0⟩) = _ at first
  have firstFrame : SourceMachine.fieldTapes .input .«variables» t0
      (encodeWord m ++ clauseBits) (encodeWord n ++ t0 .«variables») =
      firstTapes_inline_RawInitialMachineStart n m clauseBits := by
    funext k
    cases k <;> simp [SourceMachine.fieldTapes, t0, inputTapes, firstTapes_inline_RawInitialMachineStart]
  rw [firstFrame] at first
  have second := (SourceMachine.fieldInTime .input .counter (by decide)
    (.headerStart 1) (.headerLoop 1) (some .scanN) program rfl rfl
    (firstTapes_inline_RawInitialMachineStart n m clauseBits) m clauseBits rfl (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[m + 2]
    (some ⟨some (.headerStart 1), initialState, firstTapes_inline_RawInitialMachineStart n m clauseBits⟩) = _ at second
  have secondFrame : SourceMachine.fieldTapes .input .counter (firstTapes_inline_RawInitialMachineStart n m clauseBits)
      clauseBits (encodeWord m ++ firstTapes_inline_RawInitialMachineStart n m clauseBits .counter) =
      counterTapes n m clauseBits := by
    funext k
    cases k <;> simp [SourceMachine.fieldTapes, firstTapes_inline_RawInitialMachineStart, counterTapes]
  rw [secondFrame] at second
  have total := trace_trans_inline_RawInitialMachineStart _ first second
  rw [show (n + 2) + (m + 2) = n + m + 4 by omega] at total
  rw [initList_eq]
  exact total

theorem headersTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 4 * m + 8]
      (some ⟨some .scanN, initialState, counterTapes n m clauseBits⟩) =
      some ⟨some .initializeIndex, initialState, headerTapes_inline_RawInitialMachineStart n m clauseBits⟩ := by
  have h := MachineInitialHeaders.headerTrace .«variables» .counter .scratch .reversed
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    .scanN .restoreN .scanM1 .restoreM1 .closeFirst .scanM6 .restoreM6 .closeSecond
    (some .initializeIndex) program rfl rfl rfl rfl rfl rfl rfl rfl
    (counterTapes n m clauseBits) n m [] []
    (by simp [counterTapes]) (by simp [counterTapes]) rfl
    (false, false, false) none
  have frame : Function.update (counterTapes n m clauseBits) .reversed
      ((encodeWords [n + m + 1, 6 * m + 1]).reverse ++
        counterTapes n m clauseBits .reversed) = headerTapes_inline_RawInitialMachineStart n m clauseBits := by
    funext k
    cases k <;> simp [counterTapes, headerTapes_inline_RawInitialMachineStart]
  rw [frame] at h
  exact h

theorem initializeIndexTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .initializeIndex, initialState, headerTapes_inline_RawInitialMachineStart n m clauseBits⟩) =
      some ⟨some .guard, initialState, startTapes n m clauseBits⟩ := by
  simp only [Function.iterate_one, MachineComposition.advance_some]
  change some (TM2.stepAux (program .initializeIndex) initialState
    (headerTapes_inline_RawInitialMachineStart n m clauseBits)) = _
  simp only [program, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp [headerTapes_inline_RawInitialMachineStart, startTapes]

theorem startTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[3 * n + 5 * m + 13]
      (some (initList machine (encodeWords [n, m] ++ clauseBits))) =
      some ⟨some .guard, initialState, startTapes n m clauseBits⟩ := by
  have total := trace_trans_inline_RawInitialMachineStart _
    (trace_trans_inline_RawInitialMachineStart _ (readCountersTrace n m clauseBits) (headersTrace n m clauseBits))
    (initializeIndexTrace n m clauseBits)
  simpa only [show (n + m + 4) + (2 * n + 4 * m + 8) + 1 =
    3 * n + 5 * m + 13 by omega] using total

theorem formulaStartTrace (F : Target.Formula) :
    (MachineComposition.advance (TM2.step program))^[
        3 * F.«variables» + 5 * F.clauses.length + 13]
      (some (initList machine (formulaBits F))) =
      some ⟨some .guard, initialState,
        startTapes F.«variables» F.clauses.length
          (encodeWords (F.clauses.flatMap clauseWords))⟩ := by
  simpa only [formulaBits, formulaWords, encodeWords_append] using
    startTrace F.«variables» F.clauses.length (encodeWords (F.clauses.flatMap clauseWords))

def startInTime (n m : ℕ) (clauseBits : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (initList machine (encodeWords [n, m] ++ clauseBits))
      (some ⟨some .guard, initialState, startTapes n m clauseBits⟩)
      (3 * n + 5 * m + 13) where
  steps := 3 * n + 5 * m + 13
  evals_in_steps := startTrace n m clauseBits
  steps_le_m := Nat.le_refl _

def formulaStartInTime (F : Target.Formula) :
    StateTransition.EvalsToInTime (TM2.step program) (initList machine (formulaBits F))
      (some ⟨some .guard, initialState,
        startTapes F.«variables» F.clauses.length
          (encodeWords (F.clauses.flatMap clauseWords))⟩)
      (3 * F.«variables» + 5 * F.clauses.length + 13) where
  steps := 3 * F.«variables» + 5 * F.clauses.length + 13
  evals_in_steps := formulaStartTrace F
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.PCP.RawInitialMachineStart

end

section

namespace DFVSGames.Foundations.PCP.RawInitialMachineLoopData

open Target Complexity RawInitialMachineModel

def clauseInput {n : Nat} (clauses : List (Clause n)) : List Bool :=
  encodeWords (clauses.flatMap Complexity.clauseWords)

@[simp] theorem clauseInput_nil (n : Nat) : clauseInput ([] : List (Clause n)) = [] := rfl

@[simp] theorem clauseInput_cons {n : Nat} (c : Clause n) (cs : List (Clause n)) :
    clauseInput (c :: cs) = encodeWords (Complexity.clauseWords c) ++ clauseInput cs := by
  simp only [clauseInput, List.flatMap_cons, encodeWords_append]

def clauseOutput (n i : Nat) (clauses : List (Clause n)) : List Nat :=
  (clauses.mapIdx fun offset c => RawInitialRows.clauseWords n (i + offset)
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c)).flatten

private theorem mapIdx_ofFn_inline_RawInitialMachineLoopData {α β : Type} (xs : List α) (f : Nat → α → β) :
    xs.mapIdx f = List.ofFn (fun i : Fin xs.length => f i.val (xs.get i)) := by
  induction xs generalizing f with
  | nil => simp
  | cons x xs ih => simp [ih]

@[simp] theorem clauseOutput_nil (n i : Nat) : clauseOutput n i [] = [] := rfl

@[simp] theorem clauseOutput_cons (n i : Nat) (c : Clause n) (cs : List (Clause n)) :
    clauseOutput n i (c :: cs) =
      RawInitialRows.clauseWords n i (RawInitialRows.clauseNames c)
        (RawInitialRows.clauseSigns c) ++ clauseOutput n (i + 1) cs := by
  simp only [clauseOutput, List.mapIdx_cons, Nat.add_zero, List.flatten_cons,
    Nat.add_comm, Nat.add_left_comm]

theorem clauseOutput_numbered (F : Formula) :
    clauseOutput F.«variables» 0 F.clauses =
      (List.finRange F.clauses.length).flatMap (fun i =>
        RawInitialRows.clauseWords F.«variables» i.val
          (RawInitialRows.clauseNames (clauseAt F i))
          (RawInitialRows.clauseSigns (clauseAt F i))) := by
  simp only [clauseOutput, mapIdx_ofFn_inline_RawInitialMachineLoopData, List.ofFn_eq_map,
    Nat.zero_add, clauseAt]
  rfl

theorem tableWords_decomposition (F : Formula) :
    GraphTables.tableWords (RawInitialTables.table F) =
      [F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
        clauseOutput F.«variables» 0 F.clauses ++
          RawInitialRows.dummyWords F.«variables» F.clauses.length := by
  rw [RawInitialRows.tableWords_eq, clauseOutput_numbered]

def loopTapes (n i remaining : Nat) (input reversed : List Bool) : Tape → List Bool
  | .input => input
  | .«variables» => encodeWord n
  | .counter => encodeWord remaining
  | .index => encodeWord i
  | .reversed => reversed
  | _ => []

theorem startTapes_eq (n m : Nat) (input : List Bool) :
    RawInitialMachineStart.startTapes n m input =
      loopTapes n 0 m input (encodeWords [n + m + 1, 6 * m + 1]).reverse := by
  funext tape
  cases tape <;> rfl

theorem decrement_counter (n i remaining : Nat) (input reversed : List Bool) :
    Function.update (loopTapes n i (remaining + 1) input reversed)
      Tape.counter (encodeWord remaining) = loopTapes n i remaining input reversed := by
  funext tape
  cases tape <;> simp [loopTapes]

theorem increment_index (n i remaining : Nat) (input reversed : List Bool) :
    Function.update (loopTapes n i remaining input reversed)
      Tape.index (true :: encodeWord i) = loopTapes n (i + 1) remaining input reversed := by
  funext tape
  cases tape <;> simp [loopTapes, encodeWord, List.replicate_succ]

end DFVSGames.Foundations.PCP.RawInitialMachineLoopData
end

section

namespace DFVSGames.Foundations.PCP.RawInitialMachinePhases

open Turing Complexity RawInitialMachineModel

theorem copySource_ne_scratch (phase : CopyPhase) : copySource phase ≠ Tape.scratch := by
  cases phase <;> simp [copySource]

theorem copySource_ne_reversed (phase : CopyPhase) : copySource phase ≠ Tape.reversed := by
  cases phase <;> simp [copySource]

def copyInTime (phase : CopyPhase) (base : Tape → List Bool)
    (n : Nat) (suffix : List Bool)
    (hsource : base (copySource phase) = encodeWord n ++ suffix)
    (hscratch : base .scratch = []) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.scan phase), state, base⟩
      (some ⟨some (copyNext phase), (state.1, none),
        Function.update base .reversed
          (List.replicate (copyScale phase * n) true ++ base .reversed)⟩)
      (2 * n + 2) :=
  MachineInitialHeaders.prefixInTime (copySource phase) Tape.scratch Tape.reversed
    (copySource_ne_scratch phase) (copySource_ne_reversed phase) (by decide)
    (copyScale phase) (.scan phase) (.restore phase) (some (copyNext phase))
    program rfl rfl base n suffix hsource hscratch state.1 state.2

def relationInTime (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.relation slot orientation), state, base⟩
      (some ⟨some (relationNext slot orientation), state,
        Function.update base .reversed
          (relationOutput slot orientation state ++ base .reversed)⟩) 1 :=
  MachineFiniteTable.emitInTime (K := Tape) (Λ := Label) (σ := State) (Γ := Alphabet)
    Tape.reversed
    (relationOutput slot orientation)
    stateKeys stateKeys_complete program (.relation slot orientation)
    (relationNext slot orientation) rfl state base

private theorem bitWord_head_inline_RawInitialMachinePhases (b : Bool) :
    (encodeWord (if b then 1 else 0)).head? = some b := by
  cases b <;> rfl

theorem loadSigns_step (base : Tape → List Bool) (a b c : Bool)
    (ha : base (.field 1) = encodeWord (if a then 1 else 0))
    (hb : base (.field 3) = encodeWord (if b then 1 else 0))
    (hc : base (.field 5) = encodeWord (if c then 1 else 0)) (state : State) :
    (TM2.step program) ⟨some .loadSigns, state, base⟩ =
      some ⟨some (.scan (.tailVariables 0)), ((a, b, c), none), base⟩ := by
  change some (TM2.stepAux (program .loadSigns) state base) = _
  simp only [program, TM2.stepAux, ha, hb, hc, bitWord_head_inline_RawInitialMachinePhases, Option.getD_some]

def loadSignsInTime (base : Tape → List Bool) (a b c : Bool)
    (ha : base (.field 1) = encodeWord (if a then 1 else 0))
    (hb : base (.field 3) = encodeWord (if b then 1 else 0))
    (hc : base (.field 5) = encodeWord (if c then 1 else 0)) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .loadSigns, state, base⟩
      (some ⟨some (.scan (.tailVariables 0)), ((a, b, c), none), base⟩) 1 where
  steps := 1
  evals_in_steps := loadSigns_step base a b c ha hb hc state
  steps_le_m := Nat.le_refl _

def cleanupFieldInTime (slot : Fin 6) (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanupField slot), state, base⟩
      (some ⟨some (if h : slot.val + 1 < 6 then .cleanupField ⟨slot.val + 1, h⟩
        else .incrementIndex), (state.1, none), Function.update base (.field slot) []⟩)
      ((base (.field slot)).length + 1) :=
  MachineDrain.drainInTime (.field slot) (.cleanupField slot) _ program rfl base state.1 state.2

def cleanupFinalInTime (slot : Fin 3) (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanupFinal slot), state, base⟩
      (some ⟨some (if h : slot.val + 1 < 3 then .cleanupFinal ⟨slot.val + 1, h⟩
        else .reset), (state.1, none), Function.update base (finalTape slot) []⟩)
      ((base (finalTape slot)).length + 1) :=
  MachineDrain.drainInTime (finalTape slot) (.cleanupFinal slot) _ program rfl base state.1 state.2

end DFVSGames.Foundations.PCP.RawInitialMachinePhases
end

section

namespace DFVSGames.Foundations.PCP.RawInitialMachineReadClause

open Turing Complexity Hastad RawInitialMachineModel

def fieldValue {n : ℕ} (c : Target.Clause n) (j : Fin 6) : ℕ :=
  (Complexity.clauseWords c)[j.val]'(by
    rw [Complexity.clauseWords_length]
    exact j.isLt)

def recordTapes {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool) : Tape → List Bool
  | .input => suffix
  | .field j => encodeWord (fieldValue c j)
  | k => base k

@[simp] theorem recordTapes_input {n : ℕ} (base : Tape → List Bool)
    (c : Target.Clause n) (suffix : List Bool) :
    recordTapes base c suffix .input = suffix := rfl

@[simp] theorem recordTapes_field {n : ℕ} (base : Tape → List Bool)
    (c : Target.Clause n) (suffix : List Bool) (j : Fin 6) :
    recordTapes base c suffix (.field j) = encodeWord (fieldValue c j) := rfl

theorem recordTapes_other {n : ℕ} (base : Tape → List Bool)
    (c : Target.Clause n) (suffix : List Bool) (k : Tape)
    (hi : k ≠ .input) (hf : ∀ j, k ≠ .field j) :
    recordTapes base c suffix k = base k := by
  cases k <;> try rfl
  · exact (hi rfl).elim
  · exact (hf _ rfl).elim

@[simp] theorem recordTapes_name {n : ℕ} (base : Tape → List Bool)
    (c : Target.Clause n) (suffix : List Bool) (j : Fin 3) :
    recordTapes base c suffix (.field (nameField j)) =
      encodeWord ((c)[j].variableIndex.val) := by
  fin_cases j <;> rfl

private theorem trace_trans_inline_RawInitialMachineReadClause {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem fieldsTrace {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool)
    (hinput : base .input = encodeWords (Complexity.clauseWords c) ++ suffix)
    (hempty : ∀ j, base (.field j) = []) (state : State) :
    (MachineComposition.advance (TM2.step program))^[
        (encodeWords (Complexity.clauseWords c)).length + 6]
      (some ⟨some (.fieldStart 0), state, base⟩) =
      some ⟨some .loadSigns, (state.1, none), recordTapes base c suffix⟩ := by
  let a := fieldValue c 0
  let b := fieldValue c 1
  let d := fieldValue c 2
  let e := fieldValue c 3
  let f := fieldValue c 4
  let g := fieldValue c 5
  have hwords : Complexity.clauseWords c = [a, b, d, e, f, g] := rfl
  have hin : base .input = encodeWord a ++ (encodeWords [b, d, e, f, g] ++ suffix) := by
    rw [hinput, hwords]
    simp only [encodeWords, List.append_assoc]
  let t1 := SourceMachine.afterField .input (.field 0) base a
    (encodeWords [b, d, e, f, g] ++ suffix)
  let t2 := SourceMachine.afterField .input (.field 1) t1 b
    (encodeWords [d, e, f, g] ++ suffix)
  let t3 := SourceMachine.afterField .input (.field 2) t2 d
    (encodeWords [e, f, g] ++ suffix)
  let t4 := SourceMachine.afterField .input (.field 3) t3 e
    (encodeWords [f, g] ++ suffix)
  let t5 := SourceMachine.afterField .input (.field 4) t4 f
    (encodeWords [g] ++ suffix)
  let t6 := SourceMachine.afterField .input (.field 5) t5 g suffix
  have h1 := (SourceMachine.fieldInTime .input (.field 0) (by decide)
    (.fieldStart 0) (.fieldLoop 0) (some (.fieldStart 1)) program rfl rfl
    base a (encodeWords [b, d, e, f, g] ++ suffix) hin state.1 state.2).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[a + 2]
    (some ⟨some (.fieldStart 0), state, base⟩) =
    some ⟨some (.fieldStart 1), (state.1, none), t1⟩ at h1
  have h2 := (SourceMachine.fieldInTime .input (.field 1) (by decide)
    (.fieldStart 1) (.fieldLoop 1) (some (.fieldStart 2)) program rfl rfl
    t1 b (encodeWords [d, e, f, g] ++ suffix)
    (by simp [t1, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[b + 2]
    (some ⟨some (.fieldStart 1), (state.1, none), t1⟩) =
    some ⟨some (.fieldStart 2), (state.1, none), t2⟩ at h2
  have h3 := (SourceMachine.fieldInTime .input (.field 2) (by decide)
    (.fieldStart 2) (.fieldLoop 2) (some (.fieldStart 3)) program rfl rfl
    t2 d (encodeWords [e, f, g] ++ suffix)
    (by simp [t2, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[d + 2]
    (some ⟨some (.fieldStart 2), (state.1, none), t2⟩) =
    some ⟨some (.fieldStart 3), (state.1, none), t3⟩ at h3
  have h4 := (SourceMachine.fieldInTime .input (.field 3) (by decide)
    (.fieldStart 3) (.fieldLoop 3) (some (.fieldStart 4)) program rfl rfl
    t3 e (encodeWords [f, g] ++ suffix)
    (by simp [t3, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[e + 2]
    (some ⟨some (.fieldStart 3), (state.1, none), t3⟩) =
    some ⟨some (.fieldStart 4), (state.1, none), t4⟩ at h4
  have h5 := (SourceMachine.fieldInTime .input (.field 4) (by decide)
    (.fieldStart 4) (.fieldLoop 4) (some (.fieldStart 5)) program rfl rfl
    t4 f (encodeWords [g] ++ suffix)
    (by simp [t4, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[f + 2]
    (some ⟨some (.fieldStart 4), (state.1, none), t4⟩) =
    some ⟨some (.fieldStart 5), (state.1, none), t5⟩ at h5
  have h6 := (SourceMachine.fieldInTime .input (.field 5) (by decide)
    (.fieldStart 5) (.fieldLoop 5) (some .loadSigns) program rfl rfl
    t5 g suffix
    (by simp [t5, SourceMachine.afterField, encodeWords])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[g + 2]
    (some ⟨some (.fieldStart 5), (state.1, none), t5⟩) =
    some ⟨some .loadSigns, (state.1, none), t6⟩ at h6
  have total := trace_trans_inline_RawInitialMachineReadClause _ (trace_trans_inline_RawInitialMachineReadClause _ (trace_trans_inline_RawInitialMachineReadClause _
    (trace_trans_inline_RawInitialMachineReadClause _ (trace_trans_inline_RawInitialMachineReadClause _ h1 h2) h3) h4) h5) h6
  have htime : (((((a + 2) + (b + 2)) + (d + 2)) + (e + 2)) + (f + 2)) + (g + 2) =
      (encodeWords (Complexity.clauseWords c)).length + 6 := by
    rw [hwords, encodeWords_length]
    simp
    omega
  rw [htime] at total
  have frame : t6 = recordTapes base c suffix := by
    funext k
    cases k with
    | field j =>
      fin_cases j <;>
        simp [t6, t5, t4, t3, t2, t1, SourceMachine.afterField, SourceMachine.fieldTapes,
          recordTapes, hempty, a, b, d, e, f, g]
    | _ =>
      simp [t6, t5, t4, t3, t2, t1, SourceMachine.afterField, SourceMachine.fieldTapes,
        recordTapes]
  rw [frame] at total
  exact total

theorem readClauseTrace {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool)
    (hinput : base .input = encodeWords (Complexity.clauseWords c) ++ suffix)
    (hempty : ∀ j, base (.field j) = []) (state : State) :
    (MachineComposition.advance (TM2.step program))^[
        (encodeWords (Complexity.clauseWords c)).length + 7]
      (some ⟨some (.fieldStart 0), state, base⟩) =
      some ⟨some (.scan (.tailVariables 0)), (RawInitialRows.clauseSigns c, none),
        recordTapes base c suffix⟩ := by
  have first := fieldsTrace base c suffix hinput hempty state
  have last := RawInitialMachinePhases.loadSigns_step (recordTapes base c suffix)
    (c)[0].positive (c)[1].positive (c)[2].positive rfl rfl rfl (state.1, none)
  have lastTrace : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .loadSigns, (state.1, none), recordTapes base c suffix⟩) =
      some ⟨some (.scan (.tailVariables 0)), (RawInitialRows.clauseSigns c, none),
        recordTapes base c suffix⟩ := last
  have total := trace_trans_inline_RawInitialMachineReadClause _ first lastTrace
  simpa only [show (encodeWords (Complexity.clauseWords c)).length + 6 + 1 =
    (encodeWords (Complexity.clauseWords c)).length + 7 by omega] using total

def readClauseInTime {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool)
    (hinput : base .input = encodeWords (Complexity.clauseWords c) ++ suffix)
    (hempty : ∀ j, base (.field j) = []) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.fieldStart 0), state, base⟩
      (some ⟨some (.scan (.tailVariables 0)), (RawInitialRows.clauseSigns c, none),
        recordTapes base c suffix⟩)
      ((encodeWords (Complexity.clauseWords c)).length + 7) where
  steps := (encodeWords (Complexity.clauseWords c)).length + 7
  evals_in_steps := readClauseTrace base c suffix hinput hempty state
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.PCP.RawInitialMachineReadClause

end

section

namespace DFVSGames.Foundations.PCP.RawInitialMachineRows

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

attribute [local irreducible] relationOutput RawInitialRows.relationWordsFor

private abbrev advance_inline_RawInitialMachineRows := MachineComposition.advance (TM2.step program)

def outputTapes (base : Tape → List Bool) (bits : List Bool) : Tape → List Bool :=
  Function.update base .reversed (bits ++ base .reversed)

@[simp] theorem outputTapes_reversed (base : Tape → List Bool) (bits : List Bool) :
    outputTapes base bits .reversed = bits ++ base .reversed := by simp [outputTapes]

theorem outputTapes_other (base : Tape → List Bool) (bits : List Bool)
    (tape : Tape) (h : tape ≠ .reversed) : outputTapes base bits tape = base tape := by
  simp [outputTapes, h]

@[simp] theorem outputTapes_twice (base : Tape → List Bool) (first second : List Bool) :
    outputTapes (outputTapes base first) second = outputTapes base (second ++ first) := by
  funext tape
  by_cases h : tape = .reversed
  · subst tape; simp [List.append_assoc]
  · simp [outputTapes, h]

private theorem trace_trans_inline_RawInitialMachineRows {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

private theorem copyTrace_inline_RawInitialMachineRows (phase : CopyPhase) (base : Tape → List Bool)
    (n : ℕ) (hsource : base (copySource phase) = encodeWord n)
    (hscratch : base .scratch = []) (signs : Signs) :
    advance_inline_RawInitialMachineRows^[2 * n + 2] (some ⟨some (.scan phase), (signs, none), base⟩) =
      some ⟨some (copyNext phase), (signs, none),
        outputTapes base (List.replicate (copyScale phase * n) true)⟩ :=
  (copyInTime phase base n [] (by simpa using hsource) hscratch (signs, none)).evals_in_steps

private theorem closeTailTrace_inline_RawInitialMachineRows (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (signs : Signs) :
    advance_inline_RawInitialMachineRows^[1] (some ⟨some (.closeTail slot orientation), (signs, none), base⟩) =
      some ⟨some (.scan (.reverseIndex slot orientation)), (signs, none),
        outputTapes base [false]⟩ := by
  change some (TM2.stepAux (program (.closeTail slot orientation)) (signs, none) base) = _
  rfl

private theorem closeReverseTrace_inline_RawInitialMachineRows (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (signs : Signs) :
    advance_inline_RawInitialMachineRows^[1] (some ⟨some (.closeReverse slot orientation), (signs, none), base⟩) =
      some ⟨some (.relation slot orientation), (signs, none),
        outputTapes base (encodeWord (2 * slot.val + if orientation then 0 else 1)).reverse⟩ :=
  MachineInitialHeaders.literalTrace .reversed
    (encodeWord (2 * slot.val + if orientation then 0 else 1))
    (.closeReverse slot orientation) (some (.relation slot orientation))
    program rfl base signs none

private theorem reverse_encodeWord_add_inline_RawInitialMachineRows (a b : ℕ) :
    (encodeWord b).reverse ++ List.replicate a true = (encodeWord (a + b)).reverse := by
  simp only [encodeWord, List.reverse_append, List.reverse_replicate, List.reverse_singleton]
  rw [Nat.add_comm a b, List.replicate_add]
  simp only [List.append_assoc]

def rowEndBits (slot : Fin 3) (orientation : Bool) (i : ℕ) (signs : Signs) : List Bool :=
  relationOutput slot orientation (signs, none) ++
    (encodeWord (6 * i + 2 * slot.val + if orientation then 0 else 1)).reverse ++ [false]

private theorem rowEndTrace_inline_RawInitialMachineRows (slot : Fin 3) (orientation : Bool) (base : Tape → List Bool)
    (i : ℕ) (hindex : base .index = encodeWord i) (hscratch : base .scratch = [])
    (signs : Signs) :
    advance_inline_RawInitialMachineRows^[2 * i + 5] (some ⟨some (.closeTail slot orientation), (signs, none), base⟩) =
      some ⟨some (relationNext slot orientation), (signs, none),
        outputTapes base (rowEndBits slot orientation i signs)⟩ := by
  let first := outputTapes base [false]
  let second := outputTapes first (List.replicate (6 * i) true)
  let third := outputTapes second
    (encodeWord (2 * slot.val + if orientation then 0 else 1)).reverse
  have h1 := closeTailTrace_inline_RawInitialMachineRows slot orientation base signs
  have h2 := copyTrace_inline_RawInitialMachineRows (.reverseIndex slot orientation) first i
    (by simpa [first, outputTapes, copySource] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  change advance_inline_RawInitialMachineRows^[2 * i + 2]
    (some ⟨some (.scan (.reverseIndex slot orientation)), (signs, none), first⟩) =
    some ⟨some (.closeReverse slot orientation), (signs, none), second⟩ at h2
  have h3 := closeReverseTrace_inline_RawInitialMachineRows slot orientation second signs
  have h4 := (relationInTime slot orientation third (signs, none)).evals_in_steps
  change advance_inline_RawInitialMachineRows^[1] (some ⟨some (.relation slot orientation), (signs, none), third⟩) =
    some ⟨some (relationNext slot orientation), (signs, none),
      outputTapes third (relationOutput slot orientation (signs, none))⟩ at h4
  have total := trace_trans_inline_RawInitialMachineRows _ (trace_trans_inline_RawInitialMachineRows _ (trace_trans_inline_RawInitialMachineRows _ h1 h2) h3) h4
  have hout : outputTapes third (relationOutput slot orientation (signs, none)) =
      outputTapes base (rowEndBits slot orientation i signs) := by
    simp only [third, second, first, outputTapes_twice]
    apply congrArg (outputTapes base)
    rw [reverse_encodeWord_add_inline_RawInitialMachineRows]
    simp only [rowEndBits, Nat.add_assoc, List.append_assoc]
  rw [hout] at total
  simpa only [show 1 + (2 * i + 2) + 1 + 1 = 2 * i + 5 by omega] using total

private theorem rowEndBits_append_inline_RawInitialMachineRows (slot : Fin 3) (orientation : Bool)
    (tail i : ℕ) (signs : Signs) :
    rowEndBits slot orientation i signs ++ List.replicate tail true =
      (encodeWords ([tail, 6 * i + 2 * slot.val + if orientation then 0 else 1] ++
        RawInitialRows.relationWordsFor signs (RawInitialTables.slotOrder.symm slot) orientation)).reverse := by
  simp only [rowEndBits, relationOutput, encodeWords_append, encodeWords,
    List.append_nil, List.reverse_append, encodeWord,
    List.reverse_replicate, List.reverse_singleton, List.append_assoc]

theorem falseRowTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .«variables» = encodeWord n) (hindex : base .index = encodeWord i)
    (hscratch : base .scratch = []) :
    advance_inline_RawInitialMachineRows^[2 * n + 4 * i + 9]
      (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
      some ⟨some (.scan (.variableName slot)), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
          (RawInitialTables.slotOrder.symm slot) false)).reverse⟩ := by
  let first := outputTapes base (List.replicate n true)
  let second := outputTapes first (List.replicate i true)
  have h1 := copyTrace_inline_RawInitialMachineRows (.tailVariables slot) base n hvariables hscratch signs
  have h2 := copyTrace_inline_RawInitialMachineRows (.tailIndex slot) first i
    (by simpa [first, outputTapes, copySource] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  simp only [copyScale, Nat.one_mul, copyNext] at h1 h2
  change advance_inline_RawInitialMachineRows^[2 * n + 2]
    (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
    some ⟨some (.scan (.tailIndex slot)), (signs, none), first⟩ at h1
  change advance_inline_RawInitialMachineRows^[2 * i + 2]
    (some ⟨some (.scan (.tailIndex slot)), (signs, none), first⟩) =
    some ⟨some (.closeTail slot false), (signs, none), second⟩ at h2
  have h3 := rowEndTrace_inline_RawInitialMachineRows slot false second i
    (by simpa [second, first, outputTapes] using hindex)
    (by simpa [second, first, outputTapes] using hscratch) signs
  have total := trace_trans_inline_RawInitialMachineRows _ (trace_trans_inline_RawInitialMachineRows _ h1 h2) h3
  have hout : outputTapes second (rowEndBits slot false i signs) =
      outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
        (RawInitialTables.slotOrder.symm slot) false)).reverse := by
    simp only [second, first, outputTapes_twice]
    apply congrArg (outputTapes base)
    rw [← List.replicate_add, Nat.add_comm i n, rowEndBits_append_inline_RawInitialMachineRows]
    simp only [RawInitialRows.incidenceWords, Bool.false_eq_true, ↓reduceIte,
      Equiv.apply_symm_apply]
  rw [hout] at total
  simpa only [relationNext, Bool.false_eq_true, ↓reduceIte,
    show (2 * n + 2) + (2 * i + 2) + (2 * i + 5) = 2 * n + 4 * i + 9 by omega] using total

theorem trueRowTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hname : base (.field (nameField slot)) =
      encodeWord (RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)))
    (hindex : base .index = encodeWord i) (hscratch : base .scratch = []) :
    advance_inline_RawInitialMachineRows^[2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 2 * i + 7]
      (some ⟨some (.scan (.variableName slot)), (signs, none), base⟩) =
      some ⟨some (relationNext slot true), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
          (RawInitialTables.slotOrder.symm slot) true)).reverse⟩ := by
  let value := RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)
  let first := outputTapes base (List.replicate value true)
  have h1 := copyTrace_inline_RawInitialMachineRows (.variableName slot) base value hname hscratch signs
  simp only [copyScale, Nat.one_mul, copyNext] at h1
  change advance_inline_RawInitialMachineRows^[2 * value + 2]
    (some ⟨some (.scan (.variableName slot)), (signs, none), base⟩) =
    some ⟨some (.closeTail slot true), (signs, none), first⟩ at h1
  have h2 := rowEndTrace_inline_RawInitialMachineRows slot true first i
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  have total := trace_trans_inline_RawInitialMachineRows _ h1 h2
  have hout : outputTapes first (rowEndBits slot true i signs) =
      outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
        (RawInitialTables.slotOrder.symm slot) true)).reverse := by
    simp only [first, outputTapes_twice, rowEndBits_append_inline_RawInitialMachineRows, value,
      RawInitialRows.incidenceWords, ↓reduceIte, Equiv.apply_symm_apply]
  rw [hout] at total
  simpa only [value, show (2 * value + 2) + (2 * i + 5) = 2 * value + 2 * i + 7 by omega] using total

def pairWords (slot : Fin 3) (n i : ℕ) (names : RawInitialRows.Names)
    (signs : Signs) : List ℕ :=
  RawInitialRows.incidenceWords n i names signs (RawInitialTables.slotOrder.symm slot) false ++
    RawInitialRows.incidenceWords n i names signs (RawInitialTables.slotOrder.symm slot) true

theorem pairTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .«variables» = encodeWord n) (hindex : base .index = encodeWord i)
    (hname : base (.field (nameField slot)) =
      encodeWord (RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)))
    (hscratch : base .scratch = []) :
    advance_inline_RawInitialMachineRows^[2 * n + 6 * i +
      2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 16]
      (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
      some ⟨some (relationNext slot true), (signs, none),
        outputTapes base (encodeWords (pairWords slot n i names signs)).reverse⟩ := by
  let first := outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
    (RawInitialTables.slotOrder.symm slot) false)).reverse
  have h1 := falseRowTrace slot base n i names signs hvariables hindex hscratch
  have h2 := trueRowTrace slot first n i names signs
    (by simpa [first, outputTapes] using hname)
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes] using hscratch)
  have total := trace_trans_inline_RawInitialMachineRows _ h1 h2
  simpa only [first, outputTapes_twice, pairWords, encodeWords_append, List.reverse_append,
    show (2 * n + 4 * i + 9) +
      (2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 2 * i + 7) =
      2 * n + 6 * i +
        2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 16 by omega]
    using total

theorem rowsTrace (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .«variables» = encodeWord n) (hindex : base .index = encodeWord i)
    (hname0 : base (.field 0) = encodeWord names.1)
    (hname2 : base (.field 2) = encodeWord names.2.1)
    (hname4 : base (.field 4) = encodeWord names.2.2)
    (hscratch : base .scratch = []) :
    advance_inline_RawInitialMachineRows^[6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48]
      (some ⟨some (.scan (.tailVariables 0)), (signs, none), base⟩) =
      some ⟨some (.cleanupField 0), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.clauseWords n i names signs)).reverse⟩ := by
  let first := outputTapes base (encodeWords (pairWords 0 n i names signs)).reverse
  let second := outputTapes first (encodeWords (pairWords 1 n i names signs)).reverse
  have h0 := pairTrace 0 base n i names signs hvariables hindex hname0 hscratch
  have h1 := pairTrace 1 first n i names signs
    (by simpa [first, outputTapes] using hvariables)
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes, nameField, RawInitialRows.nameWord,
      RawInitialTables.slotOrder] using hname2)
    (by simpa [first, outputTapes] using hscratch)
  have h2 := pairTrace 2 second n i names signs
    (by simpa [second, first, outputTapes] using hvariables)
    (by simpa [second, first, outputTapes] using hindex)
    (by simpa [second, first, outputTapes, nameField, RawInitialRows.nameWord,
      RawInitialTables.slotOrder] using hname4)
    (by simpa [second, first, outputTapes] using hscratch)
  change advance_inline_RawInitialMachineRows^[2 * n + 6 * i + 2 * names.1 + 16]
    (some ⟨some (.scan (.tailVariables 0)), (signs, none), base⟩) =
    some ⟨some (.scan (.tailVariables 1)), (signs, none), first⟩ at h0
  change advance_inline_RawInitialMachineRows^[2 * n + 6 * i + 2 * names.2.1 + 16]
    (some ⟨some (.scan (.tailVariables 1)), (signs, none), first⟩) =
    some ⟨some (.scan (.tailVariables 2)), (signs, none), second⟩ at h1
  change advance_inline_RawInitialMachineRows^[2 * n + 6 * i + 2 * names.2.2 + 16]
    (some ⟨some (.scan (.tailVariables 2)), (signs, none), second⟩) =
    some ⟨some (.cleanupField 0), (signs, none),
      outputTapes second (encodeWords (pairWords 2 n i names signs)).reverse⟩ at h2
  have total := trace_trans_inline_RawInitialMachineRows _ (trace_trans_inline_RawInitialMachineRows _ h0 h1) h2
  have hout : outputTapes second (encodeWords (pairWords 2 n i names signs)).reverse =
      outputTapes base (encodeWords (RawInitialRows.clauseWords n i names signs)).reverse := by
    simp only [second, first, outputTapes_twice, RawInitialRows.clauseWords,
      encodeWords_append, List.reverse_append, pairWords, List.append_assoc]
    rfl
  rw [hout] at total
  simpa only [show (2 * n + 6 * i + 2 * names.1 + 16) +
    (2 * n + 6 * i + 2 * names.2.1 + 16) + (2 * n + 6 * i + 2 * names.2.2 + 16) =
      6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48 by omega] using total

def rowsInTime (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .«variables» = encodeWord n) (hindex : base .index = encodeWord i)
    (hname0 : base (.field 0) = encodeWord names.1)
    (hname2 : base (.field 2) = encodeWord names.2.1)
    (hname4 : base (.field 4) = encodeWord names.2.2)
    (hscratch : base .scratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.scan (.tailVariables 0)), (signs, none), base⟩
      (some ⟨some (.cleanupField 0), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.clauseWords n i names signs)).reverse⟩)
      (6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48) where
  steps := 6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48
  evals_in_steps := rowsTrace base n i names signs hvariables hindex hname0 hname2 hname4 hscratch
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.PCP.RawInitialMachineRows

end

section

namespace DFVSGames.Foundations.PCP.RawInitialMachineCleanup

open Turing Complexity RawInitialMachineModel RawInitialMachineReadClause

private theorem trace_trans_inline_RawInitialMachineCleanup {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem incrementIndexTrace (base : Tape → List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .incrementIndex, state, base⟩) =
      some ⟨some .guard, state, Function.update base .index (true :: base .index)⟩ := by
  rfl

theorem cleanupTrace {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool) (i : ℕ)
    (hempty : ∀ j, base (.field j) = []) (hindex : base .index = encodeWord i)
    (incoming : State) :
    (MachineComposition.advance (TM2.step program))^[
        (encodeWords (Complexity.clauseWords c)).length + 7]
      (some ⟨some (.cleanupField 0), incoming, recordTapes base c suffix⟩) =
      some ⟨some .guard, (incoming.1, none),
        Function.update (Function.update base .input suffix) .index (encodeWord (i + 1))⟩ := by
  let r := recordTapes base c suffix
  let t1 := Function.update r (.field 0) []
  let t2 := Function.update t1 (.field 1) []
  let t3 := Function.update t2 (.field 2) []
  let t4 := Function.update t3 (.field 3) []
  let t5 := Function.update t4 (.field 4) []
  let t6 := Function.update t5 (.field 5) []
  have h1 := (RawInitialMachinePhases.cleanupFieldInTime 0 r incoming).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[
      (encodeWord (fieldValue c 0)).length + 1]
    (some ⟨some (.cleanupField 0), incoming, r⟩) =
    some ⟨some (.cleanupField 1), (incoming.1, none), t1⟩ at h1
  have h2 := (RawInitialMachinePhases.cleanupFieldInTime 1 t1 (incoming.1, none)).evals_in_steps
  have hf2 : t1 (.field 1) = encodeWord (fieldValue c 1) := by
    simp [t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t1 (.field 1)).length + 1]
    (some ⟨some (.cleanupField 1), (incoming.1, none), t1⟩) =
    some ⟨some (.cleanupField 2), (incoming.1, none), t2⟩ at h2
  rw [hf2] at h2
  have h3 := (RawInitialMachinePhases.cleanupFieldInTime 2 t2 (incoming.1, none)).evals_in_steps
  have hf3 : t2 (.field 2) = encodeWord (fieldValue c 2) := by
    simp [t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t2 (.field 2)).length + 1]
    (some ⟨some (.cleanupField 2), (incoming.1, none), t2⟩) =
    some ⟨some (.cleanupField 3), (incoming.1, none), t3⟩ at h3
  rw [hf3] at h3
  have h4 := (RawInitialMachinePhases.cleanupFieldInTime 3 t3 (incoming.1, none)).evals_in_steps
  have hf4 : t3 (.field 3) = encodeWord (fieldValue c 3) := by
    simp [t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t3 (.field 3)).length + 1]
    (some ⟨some (.cleanupField 3), (incoming.1, none), t3⟩) =
    some ⟨some (.cleanupField 4), (incoming.1, none), t4⟩ at h4
  rw [hf4] at h4
  have h5 := (RawInitialMachinePhases.cleanupFieldInTime 4 t4 (incoming.1, none)).evals_in_steps
  have hf5 : t4 (.field 4) = encodeWord (fieldValue c 4) := by
    simp [t4, t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t4 (.field 4)).length + 1]
    (some ⟨some (.cleanupField 4), (incoming.1, none), t4⟩) =
    some ⟨some (.cleanupField 5), (incoming.1, none), t5⟩ at h5
  rw [hf5] at h5
  have h6 := (RawInitialMachinePhases.cleanupFieldInTime 5 t5 (incoming.1, none)).evals_in_steps
  have hf6 : t5 (.field 5) = encodeWord (fieldValue c 5) := by
    simp [t5, t4, t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t5 (.field 5)).length + 1]
    (some ⟨some (.cleanupField 5), (incoming.1, none), t5⟩) =
    some ⟨some .incrementIndex, (incoming.1, none), t6⟩ at h6
  rw [hf6] at h6
  have last := incrementIndexTrace t6 (incoming.1, none)
  have total := trace_trans_inline_RawInitialMachineCleanup _ (trace_trans_inline_RawInitialMachineCleanup _ (trace_trans_inline_RawInitialMachineCleanup _ (trace_trans_inline_RawInitialMachineCleanup _
    (trace_trans_inline_RawInitialMachineCleanup _ (trace_trans_inline_RawInitialMachineCleanup _ h1 h2) h3) h4) h5) h6) last
  have htime :
      ((((((encodeWord (fieldValue c 0)).length + 1 +
        ((encodeWord (fieldValue c 1)).length + 1)) +
        ((encodeWord (fieldValue c 2)).length + 1)) +
        ((encodeWord (fieldValue c 3)).length + 1)) +
        ((encodeWord (fieldValue c 4)).length + 1)) +
        ((encodeWord (fieldValue c 5)).length + 1)) + 1 =
      (encodeWords (Complexity.clauseWords c)).length + 7 := by
    simp [fieldValue, Complexity.clauseWords, Complexity.literalWords, encodeWords]
    omega
  rw [htime] at total
  have frame : Function.update t6 .index (true :: t6 .index) =
      Function.update (Function.update base .input suffix) .index (encodeWord (i + 1)) := by
    funext k
    cases k with
    | field j =>
      fin_cases j <;> simp [t6, t5, t4, t3, t2, t1, r, recordTapes, hempty]
    | index =>
      simp [t6, t5, t4, t3, t2, t1, r, recordTapes, hindex,
        encodeWord, List.replicate_succ]
    | _ => simp [t6, t5, t4, t3, t2, t1, r, recordTapes]
  rw [frame] at total
  exact total

def cleanupInTime {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool) (i : ℕ)
    (hempty : ∀ j, base (.field j) = []) (hindex : base .index = encodeWord i)
    (incoming : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanupField 0), incoming, recordTapes base c suffix⟩
      (some ⟨some .guard, (incoming.1, none),
        Function.update (Function.update base .input suffix) .index (encodeWord (i + 1))⟩)
      ((encodeWords (Complexity.clauseWords c)).length + 7) where
  steps := (encodeWords (Complexity.clauseWords c)).length + 7
  evals_in_steps := cleanupTrace base c suffix i hempty hindex incoming
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.PCP.RawInitialMachineCleanup

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
