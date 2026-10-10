import Mathlib
import OAI.Computability.MinUncut.Machines.RawInitialMachineBudget
import OAI.Computability.MinUncut.Machines.MachineInitialHeaders

namespace OAI

namespace MinUncutGames.Foundations.PCP.RawInitialMachinePhases

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

private theorem bitWord_head (b : Bool) :
    (encodeWord (if b then 1 else 0)).head? = some b := by
  cases b <;> rfl

theorem loadSigns_step (base : Tape → List Bool) (a b c : Bool)
    (ha : base (.field 1) = encodeWord (if a then 1 else 0))
    (hb : base (.field 3) = encodeWord (if b then 1 else 0))
    (hc : base (.field 5) = encodeWord (if c then 1 else 0)) (state : State) :
    (TM2.step program) ⟨some .loadSigns, state, base⟩ =
      some ⟨some (.scan (.tailVariables 0)), ((a, b, c), none), base⟩ := by
  change some (TM2.stepAux (program .loadSigns) state base) = _
  simp only [program, TM2.stepAux, ha, hb, hc, bitWord_head, Option.getD_some]

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

end MinUncutGames.Foundations.PCP.RawInitialMachinePhases

namespace MinUncutGames.Foundations.PCP.RawInitialMachineReadClause

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

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
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
  have total := trace_trans _ (trace_trans _ (trace_trans _
    (trace_trans _ (trace_trans _ h1 h2) h3) h4) h5) h6
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
  have total := trace_trans _ first lastTrace
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

end MinUncutGames.Foundations.PCP.RawInitialMachineReadClause

namespace MinUncutGames.Foundations.PCP.RawInitialMachineRows

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

attribute [local irreducible] relationOutput RawInitialRows.relationWordsFor

abbrev advance := MachineComposition.advance (TM2.step program)

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

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem copyTrace (phase : CopyPhase) (base : Tape → List Bool)
    (n : ℕ) (hsource : base (copySource phase) = encodeWord n)
    (hscratch : base .scratch = []) (signs : Signs) :
    advance^[2 * n + 2] (some ⟨some (.scan phase), (signs, none), base⟩) =
      some ⟨some (copyNext phase), (signs, none),
        outputTapes base (List.replicate (copyScale phase * n) true)⟩ :=
  (copyInTime phase base n [] (by simpa using hsource) hscratch (signs, none)).evals_in_steps

private theorem closeTailTrace (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (signs : Signs) :
    advance^[1] (some ⟨some (.closeTail slot orientation), (signs, none), base⟩) =
      some ⟨some (.scan (.reverseIndex slot orientation)), (signs, none),
        outputTapes base [false]⟩ := by
  change some (TM2.stepAux (program (.closeTail slot orientation)) (signs, none) base) = _
  rfl

private theorem closeReverseTrace (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (signs : Signs) :
    advance^[1] (some ⟨some (.closeReverse slot orientation), (signs, none), base⟩) =
      some ⟨some (.relation slot orientation), (signs, none),
        outputTapes base (encodeWord (2 * slot.val + if orientation then 0 else 1)).reverse⟩ :=
  MachineInitialHeaders.literalTrace .reversed
    (encodeWord (2 * slot.val + if orientation then 0 else 1))
    (.closeReverse slot orientation) (some (.relation slot orientation))
    program rfl base signs none

private theorem reverse_encodeWord_add (a b : ℕ) :
    (encodeWord b).reverse ++ List.replicate a true = (encodeWord (a + b)).reverse := by
  simp only [encodeWord, List.reverse_append, List.reverse_replicate, List.reverse_singleton]
  rw [Nat.add_comm a b, List.replicate_add]
  simp only [List.append_assoc]

def rowEndBits (slot : Fin 3) (orientation : Bool) (i : ℕ) (signs : Signs) : List Bool :=
  relationOutput slot orientation (signs, none) ++
    (encodeWord (6 * i + 2 * slot.val + if orientation then 0 else 1)).reverse ++ [false]

private theorem rowEndTrace (slot : Fin 3) (orientation : Bool) (base : Tape → List Bool)
    (i : ℕ) (hindex : base .index = encodeWord i) (hscratch : base .scratch = [])
    (signs : Signs) :
    advance^[2 * i + 5] (some ⟨some (.closeTail slot orientation), (signs, none), base⟩) =
      some ⟨some (relationNext slot orientation), (signs, none),
        outputTapes base (rowEndBits slot orientation i signs)⟩ := by
  let first := outputTapes base [false]
  let second := outputTapes first (List.replicate (6 * i) true)
  let third := outputTapes second
    (encodeWord (2 * slot.val + if orientation then 0 else 1)).reverse
  have h1 := closeTailTrace slot orientation base signs
  have h2 := copyTrace (.reverseIndex slot orientation) first i
    (by simpa [first, outputTapes, copySource] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  change advance^[2 * i + 2]
    (some ⟨some (.scan (.reverseIndex slot orientation)), (signs, none), first⟩) =
    some ⟨some (.closeReverse slot orientation), (signs, none), second⟩ at h2
  have h3 := closeReverseTrace slot orientation second signs
  have h4 := (relationInTime slot orientation third (signs, none)).evals_in_steps
  change advance^[1] (some ⟨some (.relation slot orientation), (signs, none), third⟩) =
    some ⟨some (relationNext slot orientation), (signs, none),
      outputTapes third (relationOutput slot orientation (signs, none))⟩ at h4
  have total := trace_trans _ (trace_trans _ (trace_trans _ h1 h2) h3) h4
  have hout : outputTapes third (relationOutput slot orientation (signs, none)) =
      outputTapes base (rowEndBits slot orientation i signs) := by
    simp only [third, second, first, outputTapes_twice]
    apply congrArg (outputTapes base)
    rw [reverse_encodeWord_add]
    simp only [rowEndBits, Nat.add_assoc, List.append_assoc]
  rw [hout] at total
  simpa only [show 1 + (2 * i + 2) + 1 + 1 = 2 * i + 5 by omega] using total

private theorem rowEndBits_append (slot : Fin 3) (orientation : Bool)
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
    advance^[2 * n + 4 * i + 9]
      (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
      some ⟨some (.scan (.variableName slot)), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
          (RawInitialTables.slotOrder.symm slot) false)).reverse⟩ := by
  let first := outputTapes base (List.replicate n true)
  let second := outputTapes first (List.replicate i true)
  have h1 := copyTrace (.tailVariables slot) base n hvariables hscratch signs
  have h2 := copyTrace (.tailIndex slot) first i
    (by simpa [first, outputTapes, copySource] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  simp only [copyScale, Nat.one_mul, copyNext] at h1 h2
  change advance^[2 * n + 2]
    (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
    some ⟨some (.scan (.tailIndex slot)), (signs, none), first⟩ at h1
  change advance^[2 * i + 2]
    (some ⟨some (.scan (.tailIndex slot)), (signs, none), first⟩) =
    some ⟨some (.closeTail slot false), (signs, none), second⟩ at h2
  have h3 := rowEndTrace slot false second i
    (by simpa [second, first, outputTapes] using hindex)
    (by simpa [second, first, outputTapes] using hscratch) signs
  have total := trace_trans _ (trace_trans _ h1 h2) h3
  have hout : outputTapes second (rowEndBits slot false i signs) =
      outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
        (RawInitialTables.slotOrder.symm slot) false)).reverse := by
    simp only [second, first, outputTapes_twice]
    apply congrArg (outputTapes base)
    rw [← List.replicate_add, Nat.add_comm i n, rowEndBits_append]
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
    advance^[2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 2 * i + 7]
      (some ⟨some (.scan (.variableName slot)), (signs, none), base⟩) =
      some ⟨some (relationNext slot true), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
          (RawInitialTables.slotOrder.symm slot) true)).reverse⟩ := by
  let value := RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)
  let first := outputTapes base (List.replicate value true)
  have h1 := copyTrace (.variableName slot) base value hname hscratch signs
  simp only [copyScale, Nat.one_mul, copyNext] at h1
  change advance^[2 * value + 2]
    (some ⟨some (.scan (.variableName slot)), (signs, none), base⟩) =
    some ⟨some (.closeTail slot true), (signs, none), first⟩ at h1
  have h2 := rowEndTrace slot true first i
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  have total := trace_trans _ h1 h2
  have hout : outputTapes first (rowEndBits slot true i signs) =
      outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
        (RawInitialTables.slotOrder.symm slot) true)).reverse := by
    simp only [first, outputTapes_twice, rowEndBits_append, value,
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
    advance^[2 * n + 6 * i +
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
  have total := trace_trans _ h1 h2
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
    advance^[6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48]
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
  change advance^[2 * n + 6 * i + 2 * names.1 + 16]
    (some ⟨some (.scan (.tailVariables 0)), (signs, none), base⟩) =
    some ⟨some (.scan (.tailVariables 1)), (signs, none), first⟩ at h0
  change advance^[2 * n + 6 * i + 2 * names.2.1 + 16]
    (some ⟨some (.scan (.tailVariables 1)), (signs, none), first⟩) =
    some ⟨some (.scan (.tailVariables 2)), (signs, none), second⟩ at h1
  change advance^[2 * n + 6 * i + 2 * names.2.2 + 16]
    (some ⟨some (.scan (.tailVariables 2)), (signs, none), second⟩) =
    some ⟨some (.cleanupField 0), (signs, none),
      outputTapes second (encodeWords (pairWords 2 n i names signs)).reverse⟩ at h2
  have total := trace_trans _ (trace_trans _ h0 h1) h2
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

end MinUncutGames.Foundations.PCP.RawInitialMachineRows

namespace MinUncutGames.Foundations.PCP.RawInitialMachineCleanup

open Turing Complexity RawInitialMachineModel RawInitialMachineReadClause

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
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
  have total := trace_trans _ (trace_trans _ (trace_trans _ (trace_trans _
    (trace_trans _ (trace_trans _ h1 h2) h3) h4) h5) h6) last
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

end MinUncutGames.Foundations.PCP.RawInitialMachineCleanup

namespace MinUncutGames.Foundations.PCP.RawInitialMachineBody

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineReadClause RawInitialMachineRows RawInitialMachineBudget

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem guardTrace_succ (n i remaining : Nat) (input reversed : List Bool)
    (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .guard, state, loopTapes n i (remaining + 1) input reversed⟩) =
      some ⟨some (.fieldStart 0), (state.1, none),
        loopTapes n i remaining input reversed⟩ := by
  have h := MachineUnaryCounter.guardTrace_succ Tape.counter Label.guard
    (.fieldStart 0) (.scan .dummyVariables) program rfl
    (loopTapes n i remaining input reversed) remaining [] state.1 state.2
  have heq (r : Nat) : MachineUnaryCounter.counterTapes Tape.counter
      (loopTapes n i remaining input reversed) r [] = loopTapes n i r input reversed := by
    funext tape
    cases tape <;> simp [MachineUnaryCounter.counterTapes, loopTapes]
  simpa only [heq, Prod.mk.eta] using h

theorem guardTrace_zero (n i : Nat) (input reversed : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .guard, state, loopTapes n i 0 input reversed⟩) =
      some ⟨some (.scan .dummyVariables), (state.1, none),
        loopTapes n i 0 input reversed⟩ := by
  have h := MachineUnaryCounter.guardTrace_zero Tape.counter Label.guard
    (.fieldStart 0) (.scan .dummyVariables) program rfl
    (loopTapes n i 0 input reversed) [] state.1 state.2
  have heq : MachineUnaryCounter.counterTapes Tape.counter
      (loopTapes n i 0 input reversed) 0 [] = loopTapes n i 0 input reversed := by
    funext tape
    cases tape <;> simp [MachineUnaryCounter.counterTapes, loopTapes]
  simpa only [heq, Prod.mk.eta] using h

theorem bodyTrace {n : Nat} (i remaining : Nat) (c : Clause n)
    (suffix reversed : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[bodyTime i c]
      (some ⟨some .guard, state,
        loopTapes n i (remaining + 1)
          (encodeWords (Complexity.clauseWords c) ++ suffix) reversed⟩) =
      some ⟨some .guard, (RawInitialRows.clauseSigns c, none),
        loopTapes n (i + 1) remaining suffix
          ((encodeWords (RawInitialRows.clauseWords n i
            (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse ++ reversed)⟩ := by
  let input := encodeWords (Complexity.clauseWords c) ++ suffix
  let base := loopTapes n i remaining input reversed
  let chunk := (encodeWords (RawInitialRows.clauseWords n i
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse
  let emitted := loopTapes n i remaining input (chunk ++ reversed)
  have first := guardTrace_succ n i remaining input reversed state
  have read := readClauseTrace base c suffix rfl (fun _ => rfl) (state.1, none)
  have rows := rowsTrace (recordTapes base c suffix) n i
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c)
    rfl rfl rfl rfl rfl rfl
  have frame : outputTapes (recordTapes base c suffix) chunk =
      recordTapes emitted c suffix := by
    funext tape
    cases tape <;> simp [outputTapes, recordTapes, emitted, base, loopTapes]
  change (MachineComposition.advance (TM2.step program))^[6 * n + 18 * i +
      2 * nameSum c + 48]
    (some ⟨some (.scan (.tailVariables 0)), (RawInitialRows.clauseSigns c, none),
      recordTapes base c suffix⟩) =
    some ⟨some (.cleanupField 0), (RawInitialRows.clauseSigns c, none),
    outputTapes (recordTapes base c suffix) chunk⟩ at rows
  rw [frame] at rows
  have cleanup := RawInitialMachineCleanup.cleanupTrace emitted c suffix i
    (fun _ => rfl) rfl (RawInitialRows.clauseSigns c, none)
  have finalFrame : Function.update (Function.update emitted .input suffix)
      .index (encodeWord (i + 1)) =
      loopTapes n (i + 1) remaining suffix (chunk ++ reversed) := by
    funext tape
    cases tape <;> simp [emitted, loopTapes]
  rw [finalFrame] at cleanup
  have total := trace_trans _ (trace_trans _ (trace_trans _ first read) rows) cleanup
  have time : 1 + ((encodeWords (Complexity.clauseWords c)).length + 7) +
      (6 * n + 18 * i + 2 * nameSum c + 48) +
      ((encodeWords (Complexity.clauseWords c)).length + 7) = bodyTime i c := by
    simp only [bodyTime, nameSum]
    omega
  simpa only [time] using total

end MinUncutGames.Foundations.PCP.RawInitialMachineBody

end OAI
