import Mathlib
import OAI.Computability.MaxCut.Games.FinalCNFHeader

namespace OAI

/-!
Exact row enumeration and input/output stream identities for the concrete
final-CNF machine. Rows occur in stored order, including repeated rows.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTableAdapter

/-- The actual unprocessed suffix of the finite table's stored row indices. -/
def remainingEvents (table : GraphTables.Table) (r : Nat) : List (Fin table.darts) :=
  (List.finRange table.darts).drop r

def processedEvents (table : GraphTables.Table) (r : Nat) : List (Fin table.darts) :=
  (List.finRange table.darts).take r

def inputStream (table : GraphTables.Table) (events : List (Fin table.darts)) : List Bool :=
  events.flatMap (fun e => encodeWords (GraphTables.rowWords table.rows[e]))

def outputStream (plan : Plan) (table : GraphTables.Table)
    (events : List (Fin table.darts)) : List Bool :=
  events.flatMap (fun e => plan.flatMap (Emitter.commandBits (rowOperands table e)
    (rowRelation table e)))

@[simp] theorem remainingEvents_zero (table : GraphTables.Table) :
    remainingEvents table 0 = List.finRange table.darts := by
  simp [remainingEvents]

@[simp] theorem remainingEvents_length (table : GraphTables.Table) (r : Nat) :
    (remainingEvents table r).length = table.darts - r := by
  simp [remainingEvents]

@[simp] theorem remainingEvents_done (table : GraphTables.Table) :
    remainingEvents table table.darts = [] := by
  simp [remainingEvents]

theorem remainingEvents_cons (table : GraphTables.Table) (r : Nat) (h : r < table.darts) :
    remainingEvents table r = ⟨r, h⟩ :: remainingEvents table (r + 1) := by
  unfold remainingEvents
  rw [List.drop_eq_getElem_cons (l := List.finRange table.darts) (i := r)
    (by simpa using h)]
  simp

@[simp] theorem processedEvents_zero (table : GraphTables.Table) :
    processedEvents table 0 = [] := by simp [processedEvents]

@[simp] theorem processedEvents_done (table : GraphTables.Table) :
    processedEvents table table.darts = List.finRange table.darts := by
  simp [processedEvents]

theorem processedEvents_succ (table : GraphTables.Table) (r : Nat) (h : r < table.darts) :
    processedEvents table (r + 1) = processedEvents table r ++ [⟨r, h⟩] := by
  unfold processedEvents
  rw [List.take_succ_eq_append_getElem (l := List.finRange table.darts) (i := r)
    (by simpa using h)]
  simp

theorem processed_append_remaining (table : GraphTables.Table) (r : Nat) :
    processedEvents table r ++ remainingEvents table r = List.finRange table.darts := by
  exact List.take_append_drop r (List.finRange table.darts)

@[simp] theorem inputStream_nil (table : GraphTables.Table) : inputStream table [] = [] := rfl

@[simp] theorem inputStream_cons (table : GraphTables.Table) (e : Fin table.darts)
    (events : List (Fin table.darts)) :
    inputStream table (e :: events) =
      encodeWords (GraphTables.rowWords table.rows[e]) ++ inputStream table events := rfl

@[simp] theorem inputStream_append (table : GraphTables.Table)
    (first rest : List (Fin table.darts)) :
    inputStream table (first ++ rest) = inputStream table first ++ inputStream table rest := by
  simp only [inputStream, List.flatMap_append]

@[simp] theorem outputStream_nil (plan : Plan) (table : GraphTables.Table) :
    outputStream plan table [] = [] := rfl

@[simp] theorem outputStream_cons (plan : Plan) (table : GraphTables.Table)
    (e : Fin table.darts) (events : List (Fin table.darts)) :
    outputStream plan table (e :: events) =
      plan.flatMap (Emitter.commandBits (rowOperands table e) (rowRelation table e)) ++
        outputStream plan table events := rfl

@[simp] theorem outputStream_append (plan : Plan) (table : GraphTables.Table)
    (first rest : List (Fin table.darts)) :
    outputStream plan table (first ++ rest) =
      outputStream plan table first ++ outputStream plan table rest := by
  simp only [outputStream, List.flatMap_append]

theorem inputStream_remaining_cons (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    inputStream table (remainingEvents table r) =
      encodeWords (GraphTables.rowWords table.rows[(⟨r, h⟩ : Fin table.darts)]) ++
        inputStream table (remainingEvents table (r + 1)) := by
  rw [remainingEvents_cons table r h, inputStream_cons]

theorem outputStream_remaining_cons (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    outputStream plan table (remainingEvents table r) =
      plan.flatMap (Emitter.commandBits (rowOperands table ⟨r, h⟩)
        (rowRelation table ⟨r, h⟩)) ++
          outputStream plan table (remainingEvents table (r + 1)) := by
  rw [remainingEvents_cons table r h, outputStream_cons]

theorem outputStream_processed_succ (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    outputStream plan table (processedEvents table (r + 1)) =
      outputStream plan table (processedEvents table r) ++
        plan.flatMap (Emitter.commandBits (rowOperands table ⟨r, h⟩)
          (rowRelation table ⟨r, h⟩)) := by
  rw [processedEvents_succ table r h, outputStream_append]
  simp

theorem inputStream_split (table : GraphTables.Table) (r : Nat) :
    inputStream table (List.finRange table.darts) =
      inputStream table (processedEvents table r) ++
        inputStream table (remainingEvents table r) := by
  rw [← inputStream_append, processed_append_remaining]

theorem outputStream_split (plan : Plan) (table : GraphTables.Table) (r : Nat) :
    outputStream plan table (List.finRange table.darts) =
      outputStream plan table (processedEvents table r) ++
        outputStream plan table (remainingEvents table r) := by
  rw [← outputStream_append, processed_append_remaining]

private theorem encodeWords_flatMap_rows_inline_FinalCNFStream {α : Type} (rows : List α) (words : α → List Nat) :
    encodeWords (rows.flatMap words) = rows.flatMap (fun row => encodeWords (words row)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem rowList_eq_finRange_map (table : GraphTables.Table) :
    GraphTables.rowList table = (List.finRange table.darts).map (fun e => table.rows[e]) := by
  rw [← List.ofFn_eq_map, ← Vector.toList_ofFn]
  change table.rows.toList = (Vector.ofFn (fun i => table.rows[i.val])).toList
  rw [Vector.ofFn_getElem]

/-- The stream starts at exactly the row suffix left by the checked header phase. -/
theorem inputStream_all (table : GraphTables.Table) :
    inputStream table (List.finRange table.darts) = tableRowsBits (genericTable table) := by
  rw [tableRowsBits, genericTable_rowList]
  erw [List.flatMap_map]
  change inputStream table (List.finRange table.darts) =
    encodeWords ((GraphTables.rowList table).flatMap
      (fun row => GenericGraphTables.rowWords (genericRow row)))
  simp only [genericRow_words]
  rw [rowList_eq_finRange_map, List.flatMap_map, encodeWords_flatMap_rows_inline_FinalCNFStream]
  rfl

theorem inputStream_remaining_zero (table : GraphTables.Table) :
    inputStream table (remainingEvents table 0) = tableRowsBits (genericTable table) := by
  rw [remainingEvents_zero, inputStream_all]

/-- Pushing a row's reversed emission realizes extension of the forward prefix. -/
theorem outputStream_accumulator_succ (plan : Plan) (table : GraphTables.Table)
    (r : Nat) (h : r < table.darts) (header : List Bool) :
    (plan.flatMap (Emitter.commandBits (rowOperands table ⟨r, h⟩)
      (rowRelation table ⟨r, h⟩))).reverse ++
        (header ++ outputStream plan table (processedEvents table r)).reverse =
      (header ++ outputStream plan table (processedEvents table (r + 1))).reverse := by
  rw [outputStream_processed_succ plan table r h]
  simp only [List.reverse_append, List.append_assoc]

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

/-! The actual bounded loop over every stored row of the final CNF converter. -/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable

structure LoopInvariant (table : GraphTables.Table) (r : Nat) (base : Tape → List Bool) : Prop where
  input : base .input = inputStream table (remainingEvents table r)
  archive : base .archive = GraphTables.tableBits table
  vertices : base .vertices = encodeWord table.vertices
  darts : base .darts = encodeWord table.darts
  index : base .rowIndex = encodeWord r
  tail : base .tail = []
  head : base .head = []
  reverse : base .reverseIndex = []
  scratch : base .scratch = []

structure LoopRun (headerPlan plan : Plan) (table : GraphTables.Table) (r remaining : Nat)
    (base : Tape → List Bool) (ambient : Ambient) where
  finalAmbient : Ambient
  finalTapes : Tape → List Bool
  execution : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
    ⟨some .guard, ((ambient, ()), none), base⟩
    (some ⟨some .reverseOutput, ((finalAmbient, ()), none), finalTapes⟩)
    (remaining * (rowTime plan (GraphTables.tableBits table).length + 1) + 1)
  accumulator : finalTapes .accumulator =
    (outputStream plan table (remainingEvents table r)).reverse ++ base .accumulator
  output : finalTapes .output = base .output

theorem rowInvariant_succ (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (hr : r < table.darts) (base : Tape → List Bool) (invariant : LoopInvariant table r base) :
    LoopInvariant table (r + 1)
      (rowResultTapes plan base table ⟨r, hr⟩
        (inputStream table (remainingEvents table (r + 1)))) := by
  constructor
  · exact rowResult_input _ _ _ _ _
  · exact (rowResult_frame _ _ _ _ _ .archive (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.archive
  · exact (rowResult_frame _ _ _ _ _ .vertices (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.vertices
  · exact (rowResult_frame _ _ _ _ _ .darts (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.darts
  · exact rowResult_index _ _ _ _ _
  · exact rowResult_tail _ _ _ _ _
  · exact rowResult_head _ _ _ _ _
  · exact rowResult_reverse _ _ _ _ _
  · exact (rowResult_frame _ _ _ _ _ .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.scratch

theorem rowWords_nonempty (table : GraphTables.Table) (e : Fin table.darts) :
    encodeWords (GraphTables.rowWords table.rows[e]) ≠ [] := by
  simp [GraphTables.rowWords, encodeWords, encodeWord]

/-- Induction follows the actual unary row counter and the actual unconsumed
input suffix. Every iteration invokes the checked row program. -/
noncomputable def loopInTime (headerPlan plan : Plan) (table : GraphTables.Table)
    (remaining : Nat) :
    ∀ (r : Nat) (_hcount : r + remaining = table.darts) (base : Tape → List Bool)
      (ambient : Ambient), LoopInvariant table r base →
        LoopRun headerPlan plan table r remaining base ambient := by
  induction remaining with
  | zero =>
      intro r hcount base ambient invariant
      have hr : r = table.darts := by omega
      have hinput : base .input = [] := by
        simpa only [hr, remainingEvents_done, inputStream_nil] using invariant.input
      refine {
        finalAmbient := ambient
        finalTapes := base
        execution := ?_
        accumulator := ?_
        output := rfl }
      · simpa only [Nat.zero_mul, Nat.zero_add] using
          guardEndInTime headerPlan plan base ambient hinput
      · simp only [hr, remainingEvents_done, outputStream_nil, List.reverse_nil, List.nil_append]
  | succ remaining ih =>
      intro r hcount base ambient invariant
      have hr : r < table.darts := by omega
      let e : Fin table.darts := ⟨r, hr⟩
      let rest := inputStream table (remainingEvents table (r + 1))
      let next := rowResultTapes plan base table e rest
      have hinput : base .input = encodeWords (GraphTables.rowWords table.rows[e]) ++ rest := by
        rw [invariant.input, inputStream_remaining_cons table r hr]
      have hnonempty : base .input ≠ [] := by
        rw [hinput]
        exact List.append_ne_nil_of_left_ne_nil (rowWords_nonempty table e) rest
      let guardRun := guardRowInTime headerPlan plan base ambient hnonempty
      let rowRun := rowInTime headerPlan plan base table e rest hinput invariant.archive
        invariant.vertices invariant.darts invariant.index invariant.tail invariant.head
        invariant.reverse invariant.scratch ambient
      let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guardRun rowRun
      let later := ih (r + 1) (by omega) next (rowRelation table e)
        (rowInvariant_succ plan table r hr base invariant)
      let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first later.execution
      refine {
        finalAmbient := later.finalAmbient
        finalTapes := later.finalTapes
        execution := { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
        accumulator := ?_
        output := ?_ }
      · have hb := run.steps_le_m
        rw [Nat.succ_mul]
        omega
      · rw [later.accumulator, outputStream_remaining_cons plan table r hr]
        simp only [next, rowResult_accumulator, List.reverse_append, List.append_assoc]
        rfl
      · rw [later.output]
        exact rowResult_frame _ _ _ _ _ .output (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

/-!
The complete actual output-producing trace of the final CNF machine. Its
terminal configuration still contains private work tapes before the
canonical halt required by the machine interface.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

def emittedBytes (plan : Plan) (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts] ++
    outputStream plan table (List.finRange table.darts)

noncomputable def rawBudget (plan : Plan) (table : GraphTables.Table) : Nat :=
  headerTimePolynomial.eval (GraphTables.tableBits table).length +
    table.darts * (rowTime plan (GraphTables.tableBits table).length + 1) + 1 +
      (emittedBytes plan table).length + 1

structure RawRun (plan : Plan) (table : GraphTables.Table) where
  finalAmbient : Ambient
  finalTapes : Tape → List Bool
  execution : StateTransition.EvalsToInTime (machine headerPlan plan).step
    (initList (machine headerPlan plan) (GraphTables.tableBits table))
    (some ⟨none, ((finalAmbient, ()), none), finalTapes⟩) (rawBudget plan table)
  output : finalTapes .output = emittedBytes plan table

theorem header_loopInvariant (_plan : Plan) (table : GraphTables.Table) :
    LoopInvariant table 0 (headerResultTapes table.vertices table.darts
      (tableRowsBits (genericTable table))) := by
  constructor
  · rw [headerResultTapes_input, inputStream_remaining_zero]
  · rw [headerResultTapes_archive]
    exact (tableBits_header_rows (genericTable table)).symm.trans (genericTable_tableBits table)
  · rfl
  · rfl
  · exact headerResultTapes_rowIndex _ _ _
  · rfl
  · rfl
  · rfl
  · rfl

/-- The input is read from the genuine `initList` configuration. Header, every
row, final guard, and reversal are all actual transitions of this one program. -/
noncomputable def rawRun (plan : Plan) (table : GraphTables.Table) : RawRun plan table := by
  let base := headerResultTapes table.vertices table.darts (tableRowsBits (genericTable table))
  let ambient : Ambient := ((), fun _ => false)
  have headerRun : StateTransition.EvalsToInTime (machine headerPlan plan).step
      (initList (machine headerPlan plan) (GraphTables.tableBits table))
      (some ⟨some .guard, ((ambient, ()), none), base⟩)
      (headerTimePolynomial.eval (GraphTables.tableBits table).length) := by
    simpa only [genericTable_tableBits, genericTable_vertices, genericTable_darts, base, ambient]
      using initializedTableHeaderInTime plan (genericTable table)
  let loop := loopInTime headerPlan plan table table.darts 0 (by omega)
    base ambient (header_loopInvariant plan table)
  have acc : loop.finalTapes .accumulator = (emittedBytes plan table).reverse := by
    rw [loop.accumulator]
    simp only [remainingEvents_zero, base, headerResultTapes_accumulator, emittedBytes,
      List.reverse_append]
  have out : loop.finalTapes .output = [] := by
    rw [loop.output]
    rfl
  let finalTapes := Reduction.MachineTransfer.tapesAt Tape.accumulator Tape.output
    loop.finalTapes [] (emittedBytes plan table)
  have finish : StateTransition.EvalsToInTime (machine headerPlan plan).step
      ⟨some .reverseOutput, ((loop.finalAmbient, ()), none), loop.finalTapes⟩
      (some ⟨none, ((loop.finalAmbient, ()), none), finalTapes⟩)
      ((emittedBytes plan table).length + 1) := by
    have run := Reduction.MachineTransfer.transferAtInTime Tape.accumulator Tape.output
      (by decide) id false .reverseOutput none (program headerPlan plan) rfl
      loop.finalTapes (loop.finalAmbient, ()) none
    simpa only [acc, out, List.reverse_reverse, List.length_reverse, List.map_id,
      List.append_nil, finalTapes, machine, FinTM2.step] using! run
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ headerRun loop.execution
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first finish
  exact {
    finalAmbient := loop.finalAmbient
    finalTapes := finalTapes
    execution := {
      toEvalsTo := run.toEvalsTo
      steps_le_m := by
        have hb := run.steps_le_m
        unfold rawBudget
        omega }
    output := by simp [finalTapes, Reduction.MachineTransfer.tapesAt] }

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

/-!
Fixed literal templates for the twelve-query converter. All control data have
constant size: twelve query references, nine auxiliary references, ten clauses,
and three literal slots. Pattern bits remain symbolic throughout the proof.

These templates specify the actual serialized rows. Their machine execution
is proved separately in FinalCNFRow and FinalCNFComputation.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFTemplate

open Target PCP

inductive Reference where
  | query : Fin 12 → Reference
  | auxiliary : Fin 9 → Reference
  deriving DecidableEq

structure LiteralTemplate where
  reference : Reference
  positive : Bool
  deriving DecidableEq

abbrev ClauseTemplate := Vector LiteralTemplate 3

def queryLiteral (bits : Fin 12 → Bool) (i : Fin 12) : LiteralTemplate :=
  ⟨.query i, !(bits i)⟩

def auxiliaryLiteral (j : Fin 9) (positive : Bool) : LiteralTemplate :=
  ⟨.auxiliary j, positive⟩

def tautologyTemplate : ClauseTemplate :=
  #v[⟨.query 0, true⟩, ⟨.query 0, false⟩, ⟨.query 0, true⟩]

/-- The same prefix-chain clauses used by `splitLong`, in their output order. -/
def chainTemplates (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  #v[
    #v[queryLiteral bits 0, queryLiteral bits 1, auxiliaryLiteral 0 true],
    #v[auxiliaryLiteral 0 false, queryLiteral bits 2, auxiliaryLiteral 1 true],
    #v[auxiliaryLiteral 1 false, queryLiteral bits 3, auxiliaryLiteral 2 true],
    #v[auxiliaryLiteral 2 false, queryLiteral bits 4, auxiliaryLiteral 3 true],
    #v[auxiliaryLiteral 3 false, queryLiteral bits 5, auxiliaryLiteral 4 true],
    #v[auxiliaryLiteral 4 false, queryLiteral bits 6, auxiliaryLiteral 5 true],
    #v[auxiliaryLiteral 5 false, queryLiteral bits 7, auxiliaryLiteral 6 true],
    #v[auxiliaryLiteral 6 false, queryLiteral bits 8, auxiliaryLiteral 7 true],
    #v[auxiliaryLiteral 7 false, queryLiteral bits 9, auxiliaryLiteral 8 true],
    #v[auxiliaryLiteral 8 false, queryLiteral bits 10, queryLiteral bits 11]]

def blockTemplates (accepted : Bool) (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  if accepted then Vector.replicate 10 tautologyTemplate else chainTemplates bits

def templates (accepted : Bool) (bits : Fin 12 → Bool) : List ClauseTemplate :=
  (blockTemplates accepted bits).toList

/-- Fixed clause/slot indexing for the machine's finite emission plan. -/
def literalAt (accepted : Bool) (bits : Fin 12 → Bool)
    (clause : Fin 10) (slot : Fin 3) : LiteralTemplate :=
  (blockTemplates accepted bits)[clause][slot]

@[simp] theorem templates_length (accepted : Bool) (bits : Fin 12 → Bool) :
    (templates accepted bits).length = 10 := Vector.length_toList

theorem templates_true (bits : Fin 12 → Bool) :
    templates true bits = List.replicate 10 tautologyTemplate := by rfl

theorem templates_false (bits : Fin 12 → Bool) :
    templates false bits = (chainTemplates bits).toList := by rfl

def literalTemplates (accepted : Bool) (bits : Fin 12 → Bool) : List LiteralTemplate :=
  (templates accepted bits).flatMap fun c => [(c)[0], (c)[1], (c)[2]]

theorem literalTemplates_length (accepted : Bool) (bits : Fin 12 → Bool) :
    (literalTemplates accepted bits).length = 30 := by
  unfold literalTemplates
  rw [VerifierToCNF.length_flatMap_constant _ _ 3 (by intro c hc; rfl), templates_length]

def literalWords (index : Reference → Nat) (literal : LiteralTemplate) : List Nat :=
  [index literal.reference, if literal.positive then 1 else 0]

def clauseWords (index : Reference → Nat) (clause : ClauseTemplate) : List Nat :=
  literalWords index clause[0] ++ literalWords index clause[1] ++ literalWords index clause[2]

def words (accepted : Bool) (bits : Fin 12 → Bool) (index : Reference → Nat) : List Nat :=
  (templates accepted bits).flatMap (clauseWords index)

theorem words_length (accepted : Bool) (bits : Fin 12 → Bool) (index : Reference → Nat) :
    (words accepted bits index).length = 60 := by
  unfold words
  rw [VerifierToCNF.length_flatMap_constant _ _ 6
    (by intro c hc; simp [clauseWords, literalWords]), templates_length]

variable (V : VerifierToCNF.FiniteVerifier 12) (e : Fin V.events)
  (p : VerifierToCNF.PatternIndex 12)

def resolve : Reference → Fin (VerifierToCNF.outputVariables V)
  | .query i => VerifierToCNF.oldIndex V (V.query e i)
  | .auxiliary j => VerifierToCNF.freshIndex V e p j

theorem resolve_query_value (i : Fin 12) :
    (resolve V e p (.query i)).val = (V.query e i).val := by
  simp only [resolve, VerifierToCNF.oldIndex, Fin.val_castAdd]

theorem resolve_auxiliary_value (j : Fin 9) :
    (resolve V e p (.auxiliary j)).val =
      V.«variables» + ((e.val * 4096 + p.val) * 9 + j.val) := by
  change (VerifierToCNF.freshIndex V e p j).val = _
  exact (VerifierToCNF.freshIndex_value V e p j).trans
    (congrArg (fun k : Nat => V.«variables» + ((e.val * k + p.val) * 9 + j.val))
      (show (VerifierToCNF.patterns 12).length = 4096 from VerifierToCNF.patterns_length 12))

def instantiateLiteral (literal : LiteralTemplate) : Literal (VerifierToCNF.outputVariables V) :=
  ⟨resolve V e p literal.reference, literal.positive⟩

def instantiateClause (clause : ClauseTemplate) : Clause (VerifierToCNF.outputVariables V) :=
  #v[instantiateLiteral V e p clause[0], instantiateLiteral V e p clause[1],
    instantiateLiteral V e p clause[2]]

/-- A symbolic twelve-input chain expands to exactly these ten clauses. -/
theorem splitLong_twelve {n : Nat} (ls : Fin 12 → Literal n) (ys : Fin 9 → Fin n) :
    VerifierToCNF.splitLong (List.ofFn ls) (List.ofFn ys) =
      [#v[ls 0, ls 1, ⟨ys 0, true⟩],
       #v[⟨ys 0, false⟩, ls 2, ⟨ys 1, true⟩],
       #v[⟨ys 1, false⟩, ls 3, ⟨ys 2, true⟩],
       #v[⟨ys 2, false⟩, ls 4, ⟨ys 3, true⟩],
       #v[⟨ys 3, false⟩, ls 5, ⟨ys 4, true⟩],
       #v[⟨ys 4, false⟩, ls 6, ⟨ys 5, true⟩],
       #v[⟨ys 5, false⟩, ls 7, ⟨ys 6, true⟩],
       #v[⟨ys 6, false⟩, ls 8, ⟨ys 7, true⟩],
       #v[⟨ys 7, false⟩, ls 9, ⟨ys 8, true⟩],
       #v[⟨ys 8, false⟩, ls 10, ls 11]] := by
  simp only [List.ofFn_succ, List.ofFn_zero, VerifierToCNF.splitLong]
  rfl

/-- Instantiating the fixed plan reproduces the actual converter's entire block. -/
theorem instantiate_templates :
    (templates (V.accepts e (VerifierToCNF.patternAt 12 p))
      (VerifierToCNF.patternAt 12 p)).map (instantiateClause V e p) =
        VerifierToCNF.block V (by decide) e p := by
  cases h : V.accepts e (VerifierToCNF.patternAt 12 p) with
  | false =>
      simp only [h, templates_false, VerifierToCNF.block, Bool.false_eq_true, ↓reduceIte,
        VerifierToCNF.forbiddenClause, VerifierToCNF.auxiliaryNames]
      rw [splitLong_twelve]
      rfl
  | true =>
      simp only [h, templates_true, VerifierToCNF.block, ↓reduceIte, List.map_replicate]
      rfl

theorem instantiate_templates_of_acceptance (accepted : Bool)
    (h : V.accepts e (VerifierToCNF.patternAt 12 p) = accepted) :
    (templates accepted (VerifierToCNF.patternAt 12 p)).map (instantiateClause V e p) =
      VerifierToCNF.block V (by decide) e p := by
  rw [← h]
  exact instantiate_templates V e p

theorem instantiateClause_words (clause : ClauseTemplate) :
    Complexity.clauseWords (instantiateClause V e p clause) =
      clauseWords (fun r => (resolve V e p r).val) clause := rfl

/-- The finite plan's sixty natural fields are the converter's actual row words. -/
theorem words_eq_block :
    words (V.accepts e (VerifierToCNF.patternAt 12 p)) (VerifierToCNF.patternAt 12 p)
      (fun r => (resolve V e p r).val) =
        (VerifierToCNF.block V (by decide) e p).flatMap Complexity.clauseWords := by
  rw [← instantiate_templates V e p]
  simp only [List.flatMap_map, instantiateClause_words]
  rfl

theorem block_words_length :
    ((VerifierToCNF.block V (by decide) e p).flatMap Complexity.clauseWords).length = 60 := by
  rw [← words_eq_block V e p]
  exact words_length _ _ _

end MaxCutGames.Foundations.Complexity.FinalCNFTemplate

/-!
The fixed finite emission plan for one directed graph row. All choices based
on the relation are functions of its 4096-bit finite register. Vertex counts,
endpoint names and row indices are read by preserving unary scans.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTemplate

def referenceValue (vertices tail head row pattern : Nat) : Reference → Nat
  | .query i => if i.val < 6 then 6 * tail + i.val else 6 * head + (i.val - 6)
  | .auxiliary j => 6 * vertices + 36864 * row + (9 * pattern + j.val)

def auxiliaryFlag : Reference → Bool
  | .query _ => false
  | .auxiliary _ => true

def tailFlag : Reference → Bool
  | .query i => decide (i.val < 6)
  | .auxiliary _ => false

def headFlag : Reference → Bool
  | .query i => decide (6 ≤ i.val)
  | .auxiliary _ => false

theorem pattern_lt (p : VerifierToCNF.PatternIndex 12) : p.val < 4096 := by
  have hlen : (VerifierToCNF.patterns 12).length = 4096 := VerifierToCNF.patterns_length 12
  exact lt_of_lt_of_eq p.isLt hlen

def referenceOffset (p : VerifierToCNF.PatternIndex 12) : Reference → Fin 36864
  | .query i => ⟨if i.val < 6 then i.val else i.val - 6, by split <;> omega⟩
  | .auxiliary j => ⟨9 * p.val + j.val, by have hp := pattern_lt p; omega⟩

/-- Seven real commands for the two unary fields of a literal. -/
def literalPlan (p : VerifierToCNF.PatternIndex 12) (literal : Ambient → LiteralTemplate) : Plan :=
  [.scaledIf 0 6 (fun state => auxiliaryFlag (literal state).reference),
   .scaledIf 2 6 (fun state => tailFlag (literal state).reference),
   .scaledIf 3 6 (fun state => headFlag (literal state).reference),
   .scaledIf 4 36864 (fun state => auxiliaryFlag (literal state).reference),
   .bounded (fun state => referenceOffset p (literal state).reference),
   .literal [false],
   .bit (fun state => (literal state).positive)]

theorem literalPlan_length (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) : (literalPlan p literal).length = 7 := rfl

theorem literalPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) (vertices darts tail head row : Nat)
    (ambient : Ambient) :
    (literalPlan p literal).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.literalWords
        (referenceValue vertices tail head row p.val) (literal ambient)) := by
  rcases h : literal ambient with ⟨reference, positive⟩
  cases reference with
  | query i =>
      by_cases hi : i.val < 6
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show ¬ 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
  | auxiliary j =>
      simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
        referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
        encodeWords, encodeWord, List.replicate_add, List.append_assoc,
        -List.replicate_append_replicate]
      rfl

def patternLiteral (p : VerifierToCNF.PatternIndex 12) (clause : Fin 10) (slot : Fin 3)
    (ambient : Ambient) : LiteralTemplate :=
  literalAt (ambient.2 (FinalCNFPattern.patternRelationIndex p))
    (VerifierToCNF.patternAt 12 p) clause slot

def patternPlan (p : VerifierToCNF.PatternIndex 12) : Plan :=
  (List.finRange 10).flatMap fun clause =>
    (List.finRange 3).flatMap fun slot => literalPlan p (patternLiteral p clause slot)

def rowPlan : Plan :=
  (List.finRange (VerifierToCNF.patterns 12).length).flatMap patternPlan

theorem patternPlan_length (p : VerifierToCNF.PatternIndex 12) :
    (patternPlan p).length = 210 := by
  unfold patternPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 21]
  · simp
  · intro clause hclause
    rw [VerifierToCNF.length_flatMap_constant _ _ 7]
    · simp
    · intro slot hslot
      exact literalPlan_length _ _

theorem rowPlan_length : rowPlan.length = 860160 := by
  unfold rowPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 210]
  · rw [List.length_finRange, VerifierToCNF.patterns_length]; norm_num
  · intro p hp
    exact patternPlan_length p

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem patternPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (vertices darts tail head row : Nat) (ambient : Ambient) :
    (patternPlan p).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.words
        (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) (referenceValue vertices tail head row p.val)) := by
  unfold patternPlan
  simp only [List.flatMap_assoc]
  simp_rw [literalPlan_bits]
  have hclauses :
      (List.finRange 10).map
        (fun c => (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
          (VerifierToCNF.patternAt 12 p))[c]) =
      templates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) := by
    rw [← List.ofFn_eq_map]
    change List.ofFn (fun c : Fin 10 =>
      (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p))[c.val]) = _
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
    rfl
  unfold FinalCNFTemplate.words
  rw [← hclauses, List.flatMap_map, encodeWords_flatMap]
  apply List.flatMap_congr
  intro clause hclause
  simp only [List.finRange, List.ofFn_succ, List.ofFn_zero, List.flatMap_cons,
    List.flatMap_nil, patternLiteral, literalAt, FinalCNFTemplate.clauseWords,
    encodeWords_append, List.append_nil, List.append_assoc]
  rfl

theorem referenceValue_eq_resolve (table : GraphTables.Table) (e : Fin table.darts)
    (p : VerifierToCNF.PatternIndex 12) (reference : Reference) :
    referenceValue table.vertices table.rows[e].tail.val
      table.rows[table.rows[e].reverseIndex].tail.val e.val p.val reference =
      (resolve (FinalCNFPattern.tableVerifier table) e p reference).val := by
  cases reference with
  | query i =>
      rw [resolve_query_value]
      refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
      · rw [FinalBooleanVerifier.query_tail]
        simp only [referenceValue, Fin.val_castAdd, j.isLt, ite_true]
        change 6 * table.rows[e].tail.val + j.val = j.val + 6 * table.rows[e].tail.val
        omega
      · rw [FinalBooleanVerifier.query_head]
        simp only [referenceValue, Fin.val_natAdd]
        split
        · omega
        · change 6 * table.rows[table.rows[e].reverseIndex].tail.val +
              (6 + j.val - 6) = j.val + 6 * table.rows[table.rows[e].reverseIndex].tail.val
          omega
  | auxiliary j =>
      rw [resolve_auxiliary_value]
      change 6 * table.vertices + 36864 * e.val + (9 * p.val + j.val) =
        table.vertices * 6 + ((e.val * 4096 + p.val) * 9 + j.val)
      omega

theorem rowPlan_bits (table : GraphTables.Table) (e : Fin table.darts) :
    rowPlan.flatMap (Emitter.commandBits
      (values table.vertices table.darts table.rows[e].tail.val
        table.rows[table.rows[e].reverseIndex].tail.val e.val)
      ((), fun i => table.rows[e].relation[i])) =
      encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
        (by decide) e).flatMap Complexity.clauseWords) := by
  unfold rowPlan VerifierToCNF.eventBlock
  simp only [List.flatMap_assoc]
  rw [encodeWords_flatMap]
  apply List.flatMap_congr
  intro p hp
  rw [patternPlan_bits]
  dsimp only
  rw [FinalCNFPattern.pattern_lookup_eq_verifier_accepts]
  have href := funext (referenceValue_eq_resolve table e p)
  rw [href]
  exact congrArg encodeWords (words_eq_block (FinalCNFPattern.tableVerifier table) e p)

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
