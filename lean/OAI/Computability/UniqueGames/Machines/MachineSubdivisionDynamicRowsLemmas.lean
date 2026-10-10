import OAI.Computability.UniqueGames.Machines.MachineFixedCopiesLemmas
import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Machines.MachineUnaryAffineAt
import OAI.Computability.UniqueGames.PCP.SourceLoopInitLemmas
import OAI.Computability.UniqueGames.PCP.SourceMachine
import OAI.Computability.UniqueGames.PCP.SourceRuntimeSpace
import OAI.Computability.UniqueGames.Reduction.EncodingLemmas

namespace OAI

/-!
Four-edge subdivision row emission with a physical permutation-table field.

The program depends only on the fixed identity table. Five saved endpoint words
and the entire final forward permutation table are physical tape contents. In
particular an input-dependent permutation is not inserted into a program label
or literal instruction. The last row is oriented `v → r`; for binary-vector
translations its table equals the inverse table of the original `u → v` edge.
-/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionDynamicRows

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction
open MachineSubdivisionRows (identityTable inverseTable)

/-- The last table is the actual table for the left-to-right `v → r` row. -/
def rows {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List (Constraint n q) :=
  [⟨vertices 0, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 3, identityTable q⟩,
   ⟨vertices 4, vertices 3, p⟩]

def tokens (identity : List Bool) : List (MachineFieldTemplate.Token 6) :=
  [.copy 0, .copy 1, .literal identity,
   .copy 2, .copy 1, .literal identity,
   .copy 2, .copy 3, .literal identity,
   .copy 4, .copy 3, .copy 5]

@[simp] theorem tokens_length (identity : List Bool) :
    (tokens identity).length = 12 := rfl

def fields {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    Fin 6 → List Bool :=
  ![encodeWord (vertices 0).val, encodeWord (vertices 1).val,
    encodeWord (vertices 2).val, encodeWord (vertices 3).val,
    encodeWord (vertices 4).val, encodeWords (tableWords p)]

def rowBits {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List Bool := encodeWords ((rows vertices p).flatMap constraintWords)

theorem templateOutput_rows {n q : Nat} (vertices : Fin 5 → Fin n)
    (p : PermutationTable q) :
    MachineFieldTemplate.templateOutput
      (tokens (encodeWords (tableWords (identityTable q)))) (fields vertices p) =
      rowBits vertices p := by
  simp [MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput,
    tokens, fields, rowBits, rows, constraintWords, encodeWords]

/-- Six preserved fields, scratch, and a reversed-output accumulator. -/
def field (j : Fin 6) : Fin 8 := ⟨j.val, by omega⟩

def scratch : Fin 8 := 6
def output : Fin 8 := 7

theorem field_ne_scratch (j : Fin 6) : field j ≠ scratch := by
  intro h
  have := congrArg Fin.val h
  simp [field, scratch] at this
  omega

theorem field_ne_output (j : Fin 6) : field j ≠ output := by
  intro h
  have := congrArg Fin.val h
  simp [field, output] at this
  omega

theorem scratch_ne_output : scratch ≠ output := by decide

def machine (identity : List Bool) : FinTM2 where
  K := Fin 8
  k₀ := field 0
  k₁ := output
  Γ _ := Bool
  Λ := MachineFieldTemplate.Label (tokens identity).length
  main := MachineFieldTemplate.startAt (tokens identity).length 0
  σ := MachineFieldTemplate.State Unit
  initialState := (((), ()), none)
  m := MachineFieldTemplate.program (tokens identity) field scratch output none

theorem machine_finiteAlphabet (identity : List Bool) :
    ∀ k, Finite ((machine identity).Γ k) := by
  intro k
  change Finite Bool
  infer_instance

/-- Literal execution of the fixed program; all six input fields are preserved. -/
def phaseInTime (identity : List Bool) (base : Fin 8 → List Bool)
    (emptyScratch : base scratch = []) (state : MachineFieldTemplate.State Unit) :
    StateTransition.EvalsToInTime (machine identity).step
      ⟨some (MachineFieldTemplate.startAt (tokens identity).length 0), state, base⟩
      (some ⟨none, MachineFieldTemplate.reset state,
        MachineFieldTemplate.outputTapes base output
          (MachineFieldTemplate.templateOutput (tokens identity)
            (fun j => base (field j)))⟩)
      (3 * MachineFieldTemplate.copiedLength (tokens identity)
        (fun j => base (field j)) + 37) := by
  exact MachineFieldTemplate.phaseInTime (tokens identity) field scratch output
    field_ne_scratch field_ne_output scratch_ne_output id none
    (MachineFieldTemplate.program (tokens identity) field scratch output none)
    (fun _ => rfl) base emptyScratch state

/-- The variable permutation table is read once; vertex words are read according
to their explicit occurrences in the four rows. -/
theorem phase_budget (identity : List Bool) (base : Fin 8 → List Bool) :
    3 * MachineFieldTemplate.copiedLength (tokens identity)
        (fun j => base (field j)) + 37 =
      3 * ((base (field 0)).length + 2 * (base (field 1)).length +
        2 * (base (field 2)).length + 2 * (base (field 3)).length +
        (base (field 4)).length + (base (field 5)).length) + 37 := by
  simp [MachineFieldTemplate.copiedLength, tokens]
  omega

/-- The inverse table of a binary translation is literally the same table. -/
theorem translation_inverse {s : Nat}
    (a b : UniqueGamesTheorem.Integration.BinaryLinear.Vector s) :
    inverseTable (Encoding.translationTable a b) = Encoding.translationTable a b := rfl

/-- Therefore the dynamic emitter serializes the same left-to-right rows as
the general subdivision emitter, including the reversed final edge. -/
theorem translation_rows {n s : Nat} (vertices : Fin 5 → Fin n)
    (a b : UniqueGamesTheorem.Integration.BinaryLinear.Vector s) :
    rows vertices (Encoding.translationTable a b) =
      MachineSubdivisionRows.rows vertices (Encoding.translationTable a b) := by
  simp only [rows, MachineSubdivisionRows.rows, translation_inverse]

end UniqueGamesTheorem.Explicit.MachineSubdivisionDynamicRows

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionProgram

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open UniqueGamesTheorem.Reduction

inductive Tape
  | input | vertices | alphabetHeader | occurrences | remaining
  | newVertices | newEdges | u | v | middle | first | last
  | permutation | permutationReverse | affineScratch | copyScratch
  | accumulator | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .vertices, .alphabetHeader, .occurrences,
  .remaining, .newVertices, .newEdges, .u, .v, .middle, .first, .last, .permutation,
  .permutationReverse, .affineScratch, .copyScratch, .accumulator, .output]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State := MachineFieldTemplate.State Unit

def initialState : State := (((), ()), none)

def headerField : Fin 3 → Tape
  | 0 => .vertices
  | 1 => .alphabetHeader
  | 2 => .occurrences

def rowField : Fin 6 → Tape
  | 0 => .u
  | 1 => .first
  | 2 => .middle
  | 3 => .last
  | 4 => .v
  | 5 => .permutation

def rowTokens (q : Nat) := MachineSubdivisionDynamicRows.tokens
  (encodeWords (tableWords (MachineSubdivisionRows.identityTable q)))

def headerTokens (q : Nat) : List (MachineFieldTemplate.Token 2) :=
  [.copy 0, .literal (encodeWord q), .copy 1]

def newHeaderField : Fin 2 → Tape
  | 0 => .newVertices
  | 1 => .newEdges

/-- Nine fixed affine passes initialize headers, the loop counter, and all three
private vertex indices. `none` means accumulate into the existing unary word. -/
structure InitOp where
  source : Tape
  destination : Tape
  coefficient : Nat
  seed : Option Nat

def initOp : Fin 9 → InitOp
  | 0 => ⟨.vertices, .newVertices, 1, some 0⟩
  | 1 => ⟨.occurrences, .newVertices, 3, none⟩
  | 2 => ⟨.occurrences, .newEdges, 4, some 0⟩
  | 3 => ⟨.vertices, .middle, 1, some 0⟩
  | 4 => ⟨.vertices, .first, 1, some 0⟩
  | 5 => ⟨.occurrences, .first, 1, none⟩
  | 6 => ⟨.vertices, .last, 1, some 1⟩
  | 7 => ⟨.occurrences, .last, 1, none⟩
  | 8 => ⟨.occurrences, .remaining, 1, some 0⟩

def clearKeys : List Tape :=
  [.input, .vertices, .alphabetHeader, .occurrences, .remaining,
   .newVertices, .newEdges, .u, .v, .middle, .first, .last,
   .permutation, .permutationReverse, .affineScratch, .copyScratch]

inductive Label (q : Nat)
  | headerStart (i : Fin 3)
  | headerRead (i : Fin 3)
  | initialize (i : Fin 9) (phase : Fin 3)
  | emitHeader (label : MachineFieldTemplate.Label (headerTokens q).length)
  | guard
  | startU | readU | startV | readV
  | readTable (completed : Fin (q + 1))
  | reverseTable
  | emitRows (label : MachineFieldTemplate.Label (rowTokens q).length)
  | drainU | drainV | drainPermutation
  | increment
  | finishStart
  | finish (label : SourceRuntimeFinish.Label clearKeys)
  deriving DecidableEq, Fintype

def headerNext {q : Nat} (i : Fin 3) : Label q :=
  if h : i.val + 1 < 3 then .headerStart ⟨i.val + 1, h⟩ else .initialize 0 0

def initNext {q : Nat} (i : Fin 9) : Label q :=
  if h : i.val + 1 < 9 then .initialize ⟨i.val + 1, h⟩ 0
  else .emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)

def rowEntry (q : Nat) : Label q :=
  .emitRows (MachineFieldTemplate.startAt (rowTokens q).length 0)

/-- A fixed finite program: the table reader counts only `q` delimiters in
finite control, while all unbounded integers are physical unary tape contents. -/
def program (q : Nat) : Label q → TM2.Stmt (fun _ : Tape => Bool) (Label q) State
  | .headerStart i => SourceMachine.fieldStart (headerField i) (.headerRead i)
  | .headerRead i => SourceMachine.fieldLoop .input (headerField i)
      (.headerRead i) (some (headerNext i))
  | .initialize i 0 =>
      match (initOp i).seed with
      | some offset => MachineUnaryAffineAt.seed (initOp i).destination offset (.initialize i 1)
      | none => .goto (fun _ => .initialize i 1)
  | .initialize i 1 => MachineUnaryAffineAt.scan (initOp i).source .affineScratch
      (initOp i).destination (initOp i).coefficient (.initialize i 1) (.initialize i 2)
  | .initialize i 2 => MachineTransfer.loopAt .affineScratch (initOp i).source
      id false (.initialize i 2) (some (initNext i))
  | .emitHeader label => MachineFieldTemplate.instruction (headerTokens q)
      newHeaderField .copyScratch .accumulator Label.emitHeader (some .guard) label
  | .guard => MachineUnaryCounter.guard .remaining .startU .finishStart
  | .startU => SourceMachine.fieldStart .u .readU
  | .readU => SourceMachine.fieldLoop .input .u .readU (some .startV)
  | .startV => SourceMachine.fieldStart .v .readV
  | .readV => SourceMachine.fieldLoop .input .v .readV (some (.readTable 0))
  | .readTable completed =>
      if h : completed.val < q then
        .pop .input (fun state head => (state.1, head))
          (.push .permutationReverse (fun state => state.2.getD false)
            (.branch (fun state => state.2.getD false)
              (.goto fun _ => .readTable completed)
              (.load (fun state => (state.1, none))
                (.goto fun _ => .readTable ⟨completed.val + 1, by omega⟩))))
      else .load (fun state => (state.1, none)) (.goto fun _ => .reverseTable)
  | .reverseTable => MachineTransfer.loopAt .permutationReverse .permutation
      id false .reverseTable (some (rowEntry q))
  | .emitRows label => MachineFieldTemplate.instruction (rowTokens q)
      rowField .copyScratch .accumulator Label.emitRows (some .drainU) label
  | .drainU => MachineDrain.drain .u .drainU (some .drainV)
  | .drainV => MachineDrain.drain .v .drainV (some .drainPermutation)
  | .drainPermutation => MachineDrain.drain .permutation .drainPermutation (some .increment)
  | .increment => .push .middle (fun _ => true)
      (.push .first (fun _ => true) (.push .first (fun _ => true)
        (.push .last (fun _ => true) (.push .last (fun _ => true)
          (.load (fun _ => initialState) (.goto fun _ => .guard))))))
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      ((), ()) Label.finish none label

def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label q
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program q

theorem machine_finiteAlphabet (q : Nat) :
    ∀ k, Finite ((machine q).Γ k) := by
  intro k
  change Finite Bool
  infer_instance

theorem rowField_injective : Function.Injective rowField := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [rowField]

theorem clearKeys_covers (k : Tape) :
    k ∈ clearKeys ∨ k = .accumulator ∨ k = .output := by
  cases k <;> simp [clearKeys]

theorem accumulator_not_mem_clearKeys : Tape.accumulator ∉ clearKeys := by decide
theorem output_not_mem_clearKeys : Tape.output ∉ clearKeys := by decide

end UniqueGamesTheorem.Explicit.MachineSubdivisionProgram

/-! Actual cleanup, output reversal, and polynomial finishing overhead. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionFinish

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineSubdivisionProgram

noncomputable def timePolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q) clearKeys.length (prefixTime + 1)

theorem haltList_eq (q : Nat) (bits : List Bool) :
    haltList (machine q) bits =
      ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  unfold haltList
  congr 1
  funext k
  (cases k <;> simp [machine, SourceRuntimeFinish.canonicalTapes, Function.update]); rfl

def finishStartInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (q := q)), initialState, base⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program q .finishStart) initialState base) = _
    simp only [program, TM2.stepAux]
    rfl
  steps_le_m := Nat.le_refl _

theorem covers (k : Tape) (ha : k ≠ .accumulator) (ho : k ≠ .output) :
    k ∈ clearKeys := by
  rcases clearKeys_covers k with h | h | h
  · exact h
  · exact False.elim (ha h)
  · exact False.elim (ho h)

noncomputable def completePrefix (q : Nat) (input : List Bool) (prefixTime : Polynomial Nat)
    (base : Tape → List Bool)
    (execution : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨some .finishStart, initialState, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base .output = []) :
    TM2OutputsInTime (machine q) input (some (base .accumulator).reverse)
      ((timePolynomial q prefixTime).eval input.length) := by
  let bridge := finishStartInTime q base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (q := q)), initialState, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys covers
    ((), ()) (Label.finish (q := q)) none (program q) (fun _ => rfl)
    base outputEmpty ((), ()) none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (machine q)
    input (prefixTime + 1) prefixRun clearKeys Tape.accumulator Tape.output
    accumulator_not_mem_clearKeys output_not_mem_clearKeys covers base outputEmpty
    (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (machine q).step
    (initList (machine q) input)
    (some (haltList (machine q) (base .accumulator).reverse)) _
  rw [haltList_eq]
  exact run

end UniqueGamesTheorem.Explicit.MachineSubdivisionFinish

/-! Exact execution of the three input-header reads of subdivision. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionHeaders

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineSubdivisionProgram

def inputTapes (bits : List Bool) : Tape → List Bool :=
  fun k => if k = .input then bits else []

def afterVertices (n : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n else []

def afterAlphabet (n q : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n
    else if k = .alphabetHeader then encodeWord q else []

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  fun k => if k = .input then body else if k = .vertices then encodeWord n
    else if k = .alphabetHeader then encodeWord q
    else if k = .occurrences then encodeWord Q else []

theorem initList_eq (q : Nat) (bits : List Bool) :
    initList (machine q) bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1

theorem first_result (n : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .vertices
      (inputTapes (encodeWord n ++ rest)) rest
      (encodeWord n ++ inputTapes (encodeWord n ++ rest) .vertices) =
      afterVertices n rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, inputTapes, afterVertices]

theorem second_result (n q : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .alphabetHeader
      (afterVertices n (encodeWord q ++ rest)) rest
      (encodeWord q ++ afterVertices n (encodeWord q ++ rest) .alphabetHeader) =
      afterAlphabet n q rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet]

theorem third_result (n q Q : Nat) (body : List Bool) :
    SourceMachine.fieldTapes Tape.input .occurrences
      (afterAlphabet n q (encodeWord Q ++ body)) body
      (encodeWord Q ++ afterAlphabet n q (encodeWord Q ++ body) .occurrences) =
      resultTapes n q Q body := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterAlphabet, resultTapes]

/-- The input headers are consumed literally; all unread constraint bits retain
their original order and no tape contains an implicit runtime number. -/
def headersInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (encodeWords [n, q, Q] ++ body))
      (some ⟨some (.initialize 0 0), initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6) := by
  have first := SourceMachine.fieldInTime Tape.input .vertices (by decide)
    (.headerStart 0 : Label q) (.headerRead 0) (some (.headerStart 1))
    (program q) rfl rfl
    (inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))) n
    (encodeWord q ++ (encodeWord Q ++ body)) rfl ((), ()) none
  rw [first_result] at first
  have second := SourceMachine.fieldInTime Tape.input .alphabetHeader (by decide)
    (.headerStart 1 : Label q) (.headerRead 1) (some (.headerStart 2))
    (program q) rfl rfl (afterVertices n (encodeWord q ++ (encodeWord Q ++ body))) q
    (encodeWord Q ++ body) rfl ((), ()) none
  rw [second_result] at second
  have third := SourceMachine.fieldInTime Tape.input .occurrences (by decide)
    (.headerStart 2 : Label q) (.headerRead 2) (some (.initialize 0 0))
    (program q) rfl rfl (afterAlphabet n q (encodeWord Q ++ body)) Q body rfl ((), ()) none
  rw [third_result] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  rw [initList_eq]
  simpa only [encodeWords, List.nil_append, List.append_assoc, machine, FinTM2.step, FinTM2.Cfg, initialState]
    using! ({
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        omega } : StateTransition.EvalsToInTime (TM2.step (program q))
        ⟨some (.headerStart 0), initialState,
          inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))⟩
        (some ⟨some (.initialize 0 0), initialState, resultTapes n q Q body⟩)
        (n + q + Q + 6))

theorem headers_budget (q n Q : Nat) (body : List Bool) :
    n + q + Q + 6 ≤ (encodeWords [n, q, Q] ++ body).length + 3 := by
  simp only [List.length_append, encodeWords_length, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  omega

end UniqueGamesTheorem.Explicit.MachineSubdivisionHeaders

/-! Physical header arithmetic and private-vertex initialization. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionInit

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram

theorem source_ne_scratch (i : Fin 9) : (initOp i).source ≠ Tape.affineScratch := by
  fin_cases i <;> simp [initOp]

theorem source_ne_destination (i : Fin 9) : (initOp i).source ≠ (initOp i).destination := by
  fin_cases i <;> simp [initOp]

theorem scratch_ne_destination (i : Fin 9) : Tape.affineScratch ≠ (initOp i).destination := by
  fin_cases i <;> simp [initOp]

def priorWord (seed : Option Nat) (b : Nat) : List Bool :=
  match seed with
  | none => encodeWord b
  | some _ => []

theorem operationTrace (q : Nat) (i : Fin 9) (base : Tape → List Bool) (a b : Nat)
    (sourceWord : base (initOp i).source = encodeWord a)
    (scratchEmpty : base .affineScratch = [])
    (destinationWord : base (initOp i).destination = priorWord (initOp i).seed b) :
    (MachineComposition.advance (machine q).step)^[2 * (a + 1) + 1]
      (some ⟨some (.initialize i 0), initialState, base⟩) =
      some ⟨some (initNext i), initialState,
        Function.update base (initOp i).destination
          (encodeWord ((initOp i).coefficient * a + (initOp i).seed.getD b))⟩ := by
  cases seedValue : (initOp i).seed with
  | some offset =>
    have run := MachineUnaryAffineAt.seededAffineTrace
      (initOp i).source Tape.affineScratch (initOp i).destination
      (source_ne_scratch i) (source_ne_destination i) (scratch_ne_destination i)
      (initOp i).coefficient offset
      (.initialize i 0 : Label q) (.initialize i 1) (.initialize i 2)
      (some (initNext i)) (program q)
      (by simp [program, seedValue]) rfl rfl base a []
      (by simpa using sourceWord) scratchEmpty ((), ()) none
    have hd : base (initOp i).destination = [] := by
      simpa [priorWord, seedValue] using destinationWord
    simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState, hd, List.append_nil, seedValue,
      Option.getD_some] using! run
  | none =>
    have hd : base (initOp i).destination = encodeWord b := by
      simpa [priorWord, seedValue] using destinationWord
    have frame (word : List Bool) :
        MachineUnaryAffineAt.tapes (initOp i).source Tape.affineScratch
          (initOp i).destination base (encodeWord a ++ []) [] word =
        Function.update base (initOp i).destination word := by
      simp only [List.append_nil]
      rw [← sourceWord, ← scratchEmpty]
      simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes,
        Function.update_eq_self]
    have run := MachineUnaryAffineAt.affineTrace
      (initOp i).source Tape.affineScratch (initOp i).destination
      (source_ne_scratch i) (source_ne_destination i) (scratch_ne_destination i)
      (initOp i).coefficient (.initialize i 1 : Label q) (.initialize i 2)
      (some (initNext i)) (program q) rfl rfl base a b [] [] ((), ()) none
    rw [frame, frame] at run
    simp only [List.append_nil, ← hd, Function.update_eq_self] at run
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (machine q).step)^[2 * (a + 1)]
      (some (TM2.stepAux (program q (.initialize i 0)) initialState base)) = _
    simp only [program, seedValue, TM2.stepAux]
    simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState, seedValue, Option.getD_none] using! run

def sourceValue (n Q : Nat) : Fin 9 → Nat
  | 0 => n
  | 1 => Q
  | 2 => Q
  | 3 => n
  | 4 => n
  | 5 => Q
  | 6 => n
  | 7 => Q
  | 8 => Q

def beforeValue (n : Nat) : Fin 9 → Nat
  | 0 => 0
  | 1 => n
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => n
  | 6 => 0
  | 7 => n + 1
  | 8 => 0

def afterValue (n Q : Nat) (i : Fin 9) : Nat :=
  (initOp i).coefficient * sourceValue n Q i + (initOp i).seed.getD (beforeValue n i)

def frame (n q Q : Nat) (body : List Bool) : Nat → Tape → List Bool
  | 0 => MachineSubdivisionHeaders.resultTapes n q Q body
  | r + 1 => if h : r < 9 then
      Function.update (frame n q Q body r) (initOp ⟨r, h⟩).destination
        (encodeWord (afterValue n Q ⟨r, h⟩))
    else frame n q Q body r

theorem frame_source (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val (initOp i).source = encodeWord (sourceValue n Q i) := by
  fin_cases i <;>
    simp [frame, sourceValue, initOp, MachineSubdivisionHeaders.resultTapes]

theorem frame_scratch (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val .affineScratch = [] := by
  fin_cases i <;> simp [frame, initOp, MachineSubdivisionHeaders.resultTapes]

theorem frame_destination (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val (initOp i).destination =
      priorWord (initOp i).seed (beforeValue n i) := by
  fin_cases i <;> simp [frame, initOp, MachineSubdivisionHeaders.resultTapes,
    afterValue, sourceValue, beforeValue, priorWord]

def atStage (q r : Nat) : Label q :=
  if h : r < 9 then .initialize ⟨r, h⟩ 0
  else .emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)

theorem initNext_eq_atStage (q : Nat) (i : Fin 9) :
    (initNext i : Label q) = atStage q (i.val + 1) := by
  simp [initNext, atStage]

def stageCost (n Q : Nat) : Nat := 2 * (n + Q + 1) + 1

theorem sourceValue_le (n Q : Nat) (i : Fin 9) : sourceValue n Q i ≤ n + Q := by
  fin_cases i <;> simp [sourceValue]

def prefixInTime (q n Q : Nat) (body : List Bool) (r : Nat) (hr : r ≤ 9) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.initialize 0 0), initialState, MachineSubdivisionHeaders.resultTapes n q Q body⟩
      (some ⟨some (atStage q r), initialState, frame n q Q body r⟩)
      (r * stageCost n Q) := by
  induction r with
  | zero =>
    refine { steps := 0, evals_in_steps := ?_, steps_le_m := ?_ }
    · simp [atStage, frame]
    · simp
  | succ r ih =>
    have hlt : r < 9 := by omega
    let i : Fin 9 := ⟨r, hlt⟩
    have before := ih (by omega)
    have opTrace := operationTrace q i (frame n q Q body r)
      (sourceValue n Q i) (beforeValue n i)
      (frame_source n q Q body i) (frame_scratch n q Q body i)
      (frame_destination n q Q body i)
    have op : StateTransition.EvalsToInTime (machine q).step
        ⟨some (atStage q r), initialState, frame n q Q body r⟩
        (some ⟨some (atStage q (r + 1)), initialState, frame n q Q body (r + 1)⟩)
        (stageCost n Q) := {
      steps := 2 * (sourceValue n Q i + 1) + 1
      evals_in_steps := by
        change (MachineComposition.advance (TM2.step (program q)))^[_] _ = _
        simpa only [FinTM2.step, FinTM2.Cfg, machine, atStage, hlt,
          ↓reduceDIte, i, initNext_eq_atStage, frame, afterValue] using! opTrace
      steps_le_m := by
        have bound := sourceValue_le n Q i
        dsimp [stageCost]
        omega }
    have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ before op
    exact {
      toEvalsTo := joined.toEvalsTo
      steps_le_m := by
        calc
          joined.steps ≤ stageCost n Q + r * stageCost n Q := joined.steps_le_m
          _ = (r + 1) * stageCost n Q := by
            rw [Nat.add_mul, Nat.one_mul]
            omega
    }

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  fun tape => match tape with
  | .input => body
  | .vertices => encodeWord n
  | .alphabetHeader => encodeWord q
  | .occurrences => encodeWord Q
  | .remaining => encodeWord Q
  | .newVertices => encodeWord (n + 3 * Q)
  | .newEdges => encodeWord (4 * Q)
  | .middle => encodeWord n
  | .first => encodeWord (n + Q)
  | .last => encodeWord (n + Q + 1)
  | _ => []

theorem final_frame (n q Q : Nat) (body : List Bool) :
    frame n q Q body 9 = resultTapes n q Q body := by
  funext tape
  cases tape <;>
    simp [frame, resultTapes, initOp, MachineSubdivisionHeaders.resultTapes,
      afterValue, sourceValue, beforeValue, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]

/-- The actual initialized loop counters and fresh numeric vertex IDs are
proved outputs of unary arithmetic, including the runtime vertex header. -/
def initializeInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.initialize 0 0), initialState, MachineSubdivisionHeaders.resultTapes n q Q body⟩
      (some ⟨some (.emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)),
        initialState, resultTapes n q Q body⟩)
      (9 * stageCost n Q) := by
  simpa only [atStage, show ¬ (9 < 9) by omega, ↓reduceDIte, final_frame]
    using prefixInTime q n Q body 9 (by omega)

end UniqueGamesTheorem.Explicit.MachineSubdivisionInit

/-! Literal output-header emission and the initial occurrence-loop frame. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionEmission

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram

def headerBits (n q Q : Nat) : List Bool := encodeWords [n + 3 * Q, q, 4 * Q]

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  Function.update (MachineSubdivisionInit.resultTapes n q Q body)
    .accumulator (headerBits n q Q).reverse

theorem header_template (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.templateOutput (headerTokens q)
      (fun j => MachineSubdivisionInit.resultTapes n q Q body (newHeaderField j)) =
      headerBits n q Q := by
  simp [MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput,
    headerTokens, newHeaderField, MachineSubdivisionInit.resultTapes,
    headerBits, encodeWords]

theorem header_copiedLength (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.copiedLength (headerTokens q)
      (fun j => MachineSubdivisionInit.resultTapes n q Q body (newHeaderField j)) =
      n + 7 * Q + 2 := by
  simp [MachineFieldTemplate.copiedLength, headerTokens, newHeaderField,
    MachineSubdivisionInit.resultTapes]
  omega

theorem header_result (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.outputTapes (MachineSubdivisionInit.resultTapes n q Q body)
      .accumulator (headerBits n q Q) = resultTapes n q Q body := by
  simp only [MachineFieldTemplate.outputTapes, MachineSubdivisionInit.resultTapes,
    List.append_nil, resultTapes]

def headerInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)),
        initialState, MachineSubdivisionInit.resultTapes n q Q body⟩
      (some ⟨some .guard, initialState, resultTapes n q Q body⟩)
      (3 * (n + 7 * Q + 2) + 10) := by
  have run := MachineFieldTemplate.phaseInTime (headerTokens q) newHeaderField
    Tape.copyScratch Tape.accumulator
    (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide) (by decide)
    (Label.emitHeader : MachineFieldTemplate.Label (headerTokens q).length → Label q)
    (some .guard) (program q) (fun _ => rfl)
    (MachineSubdivisionInit.resultTapes n q Q body) rfl initialState
  rw [header_template, header_copiedLength, header_result] at run
  simpa only [machine, FinTM2.step, FinTM2.Cfg, MachineFieldTemplate.reset, initialState,
    headerTokens, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
    using! run

/-- From raw input headers to the running occurrence loop, including all finite
arithmetic phases and literal output-header emission. -/
def prepareInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (encodeWords [n, q, Q] ++ body))
      (some ⟨some .guard, initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6 + 9 * MachineSubdivisionInit.stageCost n Q +
        (3 * (n + 7 * Q + 2) + 10)) := by
  have h := MachineSubdivisionHeaders.headersInTime q n Q body
  have i := MachineSubdivisionInit.initializeInTime q n Q body
  have e := headerInTime q n Q body
  have hi := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h i
  have hie := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hi e
  exact {
    toEvalsTo := hie.toEvalsTo
    steps_le_m := by
      have bound := hie.steps_le_m
      omega }

end UniqueGamesTheorem.Explicit.MachineSubdivisionEmission

end OAI
