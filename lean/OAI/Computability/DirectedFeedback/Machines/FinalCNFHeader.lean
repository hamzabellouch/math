import Mathlib
import OAI.Computability.DirectedFeedback.Machines.RawInitialMachineFinish

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

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing
open PCP.AlphabetTable

def headerFrame (input archive vertices darts rowIndex tail head accumulator : List Bool) :
    Tape → List Bool
  | .input => input
  | .archive => archive
  | .vertices => vertices
  | .darts => darts
  | .rowIndex => rowIndex
  | .tail => tail
  | .head => head
  | .accumulator => accumulator
  | _ => []

def headerInputTapes (input : List Bool) : Tape → List Bool :=
  headerFrame input [] [] [] [] [] [] []

def headerResultTapes (n m : Nat) (rowsBits : List Bool) : Tape → List Bool :=
  headerFrame rowsBits (encodeWords [n, m] ++ rowsBits)
    (encodeWord n) (encodeWord m) (encodeWord 0) [] []
    (encodeWords [6 * n + 36864 * m, 40960 * m]).reverse

@[simp] theorem headerResultTapes_input (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .input = rowsBits := rfl

@[simp] theorem headerResultTapes_archive (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .archive = encodeWords [n, m] ++ rowsBits := rfl

@[simp] theorem headerResultTapes_accumulator (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .accumulator =
      (encodeWords [6 * n + 36864 * m, 40960 * m]).reverse := rfl

@[simp] theorem headerResultTapes_rowIndex (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .rowIndex = encodeWord 0 := rfl

noncomputable def headerTimePolynomial : Polynomial Nat :=
  Polynomial.C 25 * Polynomial.X + Polynomial.C 52

@[simp] theorem headerTimePolynomial_eval (length : Nat) :
    headerTimePolynomial.eval length = 25 * length + 52 := by
  simp [headerTimePolynomial]

def headerInTime (rowPlan : Plan) (n m : Nat) (rowsBits : List Bool) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none),
        headerInputTapes (encodeWords [n, m] ++ rowsBits)⟩
      (some ⟨some .guard, ((ambient, ()), none), headerResultTapes n m rowsBits⟩)
      (headerTimePolynomial.eval (encodeWords [n, m] ++ rowsBits).length) := by
  let word := encodeWords [n, m] ++ rowsBits
  let bits := encodeWords [6 * n + 36864 * m, 40960 * m]
  let b₀ := headerInputTapes word
  let b₁ := headerFrame word word [] [] [] [] [] []
  let b₂ := headerFrame (encodeWord m ++ rowsBits) word (encodeWord n) [] [] [] [] []
  let b₃ := headerFrame rowsBits word (encodeWord n) (encodeWord m) [] [] [] []
  let b₄ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) (encodeWord 0) (encodeWord 0) []
  let b₅ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) (encodeWord 0) (encodeWord 0) bits.reverse
  let b₆ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) [] (encodeWord 0) bits.reverse
  let b₇ := headerResultTapes n m rowsBits
  have h₀ : Function.update b₀ Tape.archive (b₀ .input ++ b₀ .archive) = b₁ := by
    funext tape; cases tape <;> simp [b₀, b₁, headerInputTapes, headerFrame]
  have h₁ : Hastad.SourceMachine.fieldTapes Tape.input Tape.vertices b₁
      (encodeWord m ++ rowsBits) (encodeWord n ++ b₁ .vertices) = b₂ := by
    funext tape; cases tape <;> simp [Hastad.SourceMachine.fieldTapes, b₁, b₂, headerFrame]
  have h₂ : Hastad.SourceMachine.fieldTapes Tape.input Tape.darts b₂
      rowsBits (encodeWord m ++ b₂ .darts) = b₃ := by
    funext tape; cases tape <;> simp [Hastad.SourceMachine.fieldTapes, b₂, b₃, headerFrame]
  have h₄ : Emitter.resultTapes Tape.accumulator b₄
      (Emitter.prefixBits (Emitter.listCommands headerPlan) (values n m 0 0 0)
        ambient headerPlan.length) = b₅ := by
    rw [Emitter.bits_listCommands, headerPlan_bits]
    funext tape; cases tape <;> simp [Emitter.resultTapes, b₄, b₅, bits, headerFrame]
  have h₅ : Function.update b₅ Tape.tail [] = b₆ := by
    funext tape; cases tape <;> simp [b₅, b₆, headerFrame]
  have h₆ : Function.update b₆ Tape.head [] = b₇ := by
    funext tape; cases tape <;> simp [b₆, b₇, headerResultTapes, bits, word, headerFrame]
  have hn : n ≤ word.length := by
    simp only [word, List.length_append, encodeWords_length, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil] ; omega
  have hm : m ≤ word.length := by
    simp only [word, List.length_append, encodeWords_length, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil] ; omega
  let p₀ := MachineCopy.copyInTime Tape.input Tape.archive Tape.scratch
    (by decide) (by decide) (by decide) false .copyFirst .copySecond (some .startVertices)
    (program headerPlan rowPlan) rfl rfl b₀ (by rfl) (ambient, ()) none
  have p₀' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none), b₀⟩
      (some ⟨some .startVertices, ((ambient, ()), none), b₁⟩) (2 * (word.length + 1)) := by
    have h := p₀
    rw [h₀] at h
    simpa only [show b₀ .input = word from rfl] using h
  let p₁ := Hastad.SourceMachine.fieldInTime Tape.input Tape.vertices (by decide)
    .startVertices .readVertices (some .startDarts) (program headerPlan rowPlan)
    rfl rfl b₁ n (encodeWord m ++ rowsBits)
    (by simp [b₁, headerFrame, word, encodeWords, List.append_assoc]) (ambient, ()) none
  have p₁' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .startVertices, ((ambient, ()), none), b₁⟩
      (some ⟨some .startDarts, ((ambient, ()), none), b₂⟩) (n + 2) := by
    simpa only [h₁] using p₁
  let p₂ := Hastad.SourceMachine.fieldInTime Tape.input Tape.darts (by decide)
    .startDarts .readDarts (some .seedIndex) (program headerPlan rowPlan)
    rfl rfl b₂ m rowsBits rfl (ambient, ()) none
  have p₂' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .startDarts, ((ambient, ()), none), b₂⟩
      (some ⟨some .seedIndex, ((ambient, ()), none), b₃⟩) (m + 2) := by
    simpa only [h₂] using p₂
  let p₃ : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .seedIndex, ((ambient, ()), none), b₃⟩
      (some ⟨some (.header (Emitter.labelAt headerPlan.length 36864 0 .entry)),
        ((ambient, ()), none), b₄⟩) 1 := {
    steps := 1
    evals_in_steps := by
      simp only [Function.iterate_one]
      change TM2.step (program headerPlan rowPlan)
        ⟨some .seedIndex, ((ambient, ()), none), b₃⟩ = _
      have ht : Function.update (Function.update (Function.update b₃ Tape.rowIndex [false])
          Tape.tail [false]) Tape.head [false] = b₄ := by
        funext tape; cases tape <;> simp [b₃, b₄, headerFrame, encodeWord]
      simp only [TM2.step, program, TM2.stepAux]
      apply congrArg some
      exact congrArg (TM2.Cfg.mk _ _) ht
    steps_le_m := Nat.le_refl _ }
  let p₄ := Emitter.planInTime (Emitter.listCommands headerPlan) source Tape.scratch
    Tape.accumulator source_ne_scratch source_ne_accumulator (by decide)
    Label.header (some .headerClearTail) (program headerPlan rowPlan) (fun _ => rfl)
    (values n m 0 0 0) b₄
    (by intro i; fin_cases i <;> rfl) rfl ambient word.length
    (by
      intro i
      fin_cases i
      · exact hn
      · exact hm
      · exact Nat.zero_le _
      · exact Nat.zero_le _
      · exact Nat.zero_le _)
  have p₄' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some (.header (Emitter.labelAt headerPlan.length 36864 0 .entry)),
        ((ambient, ()), none), b₄⟩
      (some ⟨some .headerClearTail, ((ambient, ()), none), b₅⟩)
      (7 * (3 * (word.length + 1) + 3) + 1) := by
    have h := p₄
    rw [h₄] at h
    simpa only [headerPlan_length] using h
  let p₅ := MachineLookup.discardInTime Tape.tail .headerClearTail .headerClearHead
    (program headerPlan rowPlan) rfl b₅ 0 [] (by simp [b₅, headerFrame]) (ambient, ()) none
  have p₅' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headerClearTail, ((ambient, ()), none), b₅⟩
      (some ⟨some .headerClearHead, ((ambient, ()), none), b₆⟩) 1 := by
    simpa only [h₅] using p₅
  let p₆ := MachineLookup.discardInTime Tape.head .headerClearHead .guard
    (program headerPlan rowPlan) rfl b₆ 0 [] (by simp [b₆, headerFrame]) (ambient, ()) none
  have p₆' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headerClearHead, ((ambient, ()), none), b₆⟩
      (some ⟨some .guard, ((ambient, ()), none), b₇⟩) 1 := by
    simpa only [h₆] using p₆
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀' p₁'
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂'
  let p₀₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  let p₀₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃ p₄'
  let p₀₁₂₃₄₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄ p₅'
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅ p₆'
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by
      have h := p.steps_le_m
      change _ ≤ headerTimePolynomial.eval word.length
      rw [headerTimePolynomial_eval]
      omega }

def tableRowsBits (table : PCP.GenericGraphTables.Table 64) : List Bool :=
  encodeWords ((PCP.GenericGraphTables.rowList table).flatMap PCP.GenericGraphTables.rowWords)

theorem tableBits_header_rows (table : PCP.GenericGraphTables.Table 64) :
    PCP.GenericGraphTables.tableBits table =
      encodeWords [table.vertices, table.darts] ++ tableRowsBits table := by
  simp only [PCP.GenericGraphTables.tableBits, PCP.GenericGraphTables.tableWords,
    encodeWords_append, tableRowsBits]

def tableHeaderInTime (rowPlan : Plan) (table : PCP.GenericGraphTables.Table 64)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none),
        headerInputTapes (PCP.GenericGraphTables.tableBits table)⟩
      (some ⟨some .guard, ((ambient, ()), none),
        headerResultTapes table.vertices table.darts (tableRowsBits table)⟩)
      (headerTimePolynomial.eval (PCP.GenericGraphTables.tableBits table).length) := by
  rw [tableBits_header_rows]
  exact headerInTime rowPlan table.vertices table.darts (tableRowsBits table) ambient

theorem headerInput_configuration (rowPlan : Plan) (input : List Bool) :
    initList (machine headerPlan rowPlan) input =
      ⟨some .copyFirst, ((((), fun _ => false), ()), none), headerInputTapes input⟩ := by
  have ht : (initList (machine headerPlan rowPlan) input).stk = headerInputTapes input := by
    funext tape
    cases tape <;> simp [initList, machine, headerInputTapes, headerFrame]
    rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

def initializedTableHeaderInTime (rowPlan : Plan) (table : PCP.GenericGraphTables.Table 64) :
    StateTransition.EvalsToInTime (machine headerPlan rowPlan).step
      (initList (machine headerPlan rowPlan) (PCP.GenericGraphTables.tableBits table))
      (some ⟨some .guard, ((((), fun _ => false), ()), none),
        headerResultTapes table.vertices table.darts (tableRowsBits table)⟩)
      (headerTimePolynomial.eval (PCP.GenericGraphTables.tableBits table).length) := by
  rw [headerInput_configuration]
  exact tableHeaderInTime rowPlan table ((), fun _ => false)

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable

def endpointTapes (base : Tape → List Bool) (tail reverse : Nat) (rest : List Bool) :=
  Hastad.SourceMachine.fieldTapes Tape.input Tape.reverseIndex
    (Hastad.SourceMachine.fieldTapes Tape.input Tape.tail base
      (encodeWord reverse ++ rest) (encodeWord tail ++ base .tail))
    rest (encodeWord reverse ++ base .reverseIndex)

def endpointsInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (tail reverse : Nat) (rest : List Bool)
    (hinput : base .input = encodeWord tail ++ encodeWord reverse ++ rest)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .startTail, ((ambient, ()), none), base⟩
      (some ⟨some .headTableFirst, ((ambient, ()), none),
        endpointTapes base tail reverse rest⟩) (tail + reverse + 4) := by
  let first := Hastad.SourceMachine.fieldTapes Tape.input Tape.tail base
    (encodeWord reverse ++ rest) (encodeWord tail ++ base .tail)
  let run₁ := Hastad.SourceMachine.fieldInTime Tape.input Tape.tail (by decide)
    .startTail .readTail (some .startReverse) (program headerPlan plan) rfl rfl
    base tail (encodeWord reverse ++ rest) (by simpa only [List.append_assoc] using hinput)
    (ambient, ()) none
  have input₁ : first .input = encodeWord reverse ++ rest := by
    simp [first, Hastad.SourceMachine.fieldTapes]
  have reverse₁ : first .reverseIndex = base .reverseIndex := by
    simp [first, Hastad.SourceMachine.fieldTapes]
  let run₂ := Hastad.SourceMachine.fieldInTime Tape.input Tape.reverseIndex (by decide)
    .startReverse .readReverse (some .headTableFirst) (program headerPlan plan) rfl rfl
    first reverse rest input₁ (ambient, ()) none
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  simpa only [first, reverse₁, endpointTapes, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using joined

def relationInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (relation : GraphTables.RelationTable) (rest : List Bool)
    (hinput : base .input = encodeWords (GraphTables.relationWords relation) ++ rest)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .readRelation, ((ambient, ()), none), base⟩
      (some ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((((), fun i => relation[i]), ()), none), Function.update base .input rest⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .readRelation) _ _) = _
    rw [program, stepAux_readRelationAt _ _ _ _ _ _ _ _ _ hinput]
  steps_le_m := Nat.le_refl _

def emitInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (operands : Fin 5 → Nat) (hoperands : ∀ i, base (source i) = encodeWord (operands i))
    (hscratch : base .scratch = []) (ambient : Ambient)
    (N : Nat) (hbounded : ∀ i, operands i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((ambient, ()), none), base⟩
      (some ⟨some .clearTail, ((ambient, ()), none),
        Function.update base .accumulator
          ((plan.flatMap (Emitter.commandBits operands ambient)).reverse ++ base .accumulator)⟩)
      (plan.length * (3 * (N + 1) + 3) + 1) := by
  have run := Emitter.planInTime (Emitter.listCommands plan)
    source Tape.scratch Tape.accumulator source_ne_scratch source_ne_accumulator (by decide)
    Label.row (some .clearTail) (program headerPlan plan) (fun _ => rfl)
    operands base hoperands hscratch ambient N hbounded
  simpa only [Emitter.bits_listCommands, Emitter.resultTapes] using run

def finishTapes (base : Tape → List Bool) (row : Nat) : Tape → List Bool :=
  Function.update
    (Function.update (Function.update (Function.update base Tape.tail []) Tape.head [])
      Tape.reverseIndex []) Tape.rowIndex (encodeWord (row + 1))

def finishInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (tail head reverse row : Nat)
    (htail : base .tail = encodeWord tail) (hhead : base .head = encodeWord head)
    (hreverse : base .reverseIndex = encodeWord reverse)
    (hrow : base .rowIndex = encodeWord row) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .clearTail, ((ambient, ()), none), base⟩
      (some ⟨some .guard, ((ambient, ()), none), finishTapes base row⟩)
      (tail + head + reverse + 4) := by
  let t₁ := Function.update base Tape.tail []
  let t₂ := Function.update t₁ Tape.head []
  let t₃ := Function.update t₂ Tape.reverseIndex []
  let run₁ := MachineLookup.discardInTime Tape.tail .clearTail .clearHead
    (program headerPlan plan) rfl base tail [] (by simpa using htail) (ambient, ()) none
  have hhead₁ : t₁ .head = encodeWord head := by simp [t₁, hhead]
  let run₂ := MachineLookup.discardInTime Tape.head .clearHead .clearReverse
    (program headerPlan plan) rfl t₁ head [] (by simpa using hhead₁) (ambient, ()) none
  have hreverse₂ : t₂ .reverseIndex = encodeWord reverse := by simp [t₂, t₁, hreverse]
  let run₃ := MachineLookup.discardInTime Tape.reverseIndex .clearReverse .nextRow
    (program headerPlan plan) rfl t₂ reverse [] (by simpa using hreverse₂) (ambient, ()) none
  let run₄ : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .nextRow, ((ambient, ()), none), t₃⟩
      (some ⟨some .guard, ((ambient, ()), none), finishTapes base row⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program headerPlan plan .nextRow) _ _) = _
      simp only [program, TM2.stepAux]
      congr 2
      simp [t₃, t₂, t₁, finishTapes, hrow, encodeWord, List.replicate_succ]
    steps_le_m := Nat.le_refl _ }
  let r₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let r₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂ run₃
  have run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃ run₄
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using run

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program
end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFTableAdapter

open PCP

def genericRow {n m : Nat} (row : GraphTables.DartRow n m) :
    GenericGraphTables.DartRow 64 n m :=
  ⟨row.tail, row.reverseIndex, row.relation⟩

@[simp] theorem genericRow_tail {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).tail = row.tail := rfl

@[simp] theorem genericRow_reverseIndex {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).reverseIndex = row.reverseIndex := rfl

@[simp] theorem genericRow_relation {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).relation = row.relation := rfl

def genericRows {n m : Nat} (rows : GraphTables.Rows n m) :
    GenericGraphTables.Rows 64 n m := rows.map genericRow

@[simp] theorem genericRows_get {n m : Nat} (rows : GraphTables.Rows n m) (e : Fin m) :
    (genericRows rows)[e] = genericRow rows[e] := by
  simp [genericRows]

@[simp] theorem genericRows_reverseAt {n m : Nat} (rows : GraphTables.Rows n m)
    (e : Fin m) :
    GenericGraphTables.reverseAt (genericRows rows) e = GraphTables.reverseAt rows e := by
  change (genericRows rows)[e].reverseIndex = rows[e].reverseIndex
  rw [genericRows_get]
  rfl

@[simp] theorem genericRows_acceptsAt {n m : Nat} (rows : GraphTables.Rows n m)
    (e : Fin m) (a b : Fin 64) :
    GenericGraphTables.acceptsAt (genericRows rows) e a b =
      GraphTables.acceptsAt rows e a b := by
  simp only [GenericGraphTables.acceptsAt, genericRows_get, genericRow_relation]
  rfl

theorem genericRows_valid {n m : Nat} (rows : GraphTables.Rows n m)
    (valid : GraphTables.Valid rows) : GenericGraphTables.Valid (genericRows rows) := by
  constructor
  · intro e
    simpa only [genericRows_reverseAt] using valid.1 e
  · intro e a b
    simpa only [genericRows_reverseAt, genericRows_acceptsAt] using valid.2 e a b

def genericTable (table : GraphTables.Table) : GenericGraphTables.Table 64 where
  vertices := table.vertices
  darts := table.darts
  rows := genericRows table.rows
  valid := genericRows_valid table.rows table.valid

@[simp] theorem genericTable_vertices (table : GraphTables.Table) :
    (genericTable table).vertices = table.vertices := rfl

@[simp] theorem genericTable_darts (table : GraphTables.Table) :
    (genericTable table).darts = table.darts := rfl

@[simp] theorem genericTable_row (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e] = genericRow table.rows[e] := genericRows_get _ _

@[simp] theorem genericTable_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].tail = table.rows[e].tail := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericTable_reverseIndex (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].reverseIndex = table.rows[e].reverseIndex := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericTable_relation (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].relation = table.rows[e].relation := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericRow_words {n m : Nat} (row : GraphTables.DartRow n m) :
    GenericGraphTables.rowWords (genericRow row) = GraphTables.rowWords row := rfl

theorem genericTable_rowList (table : GraphTables.Table) :
    GenericGraphTables.rowList (genericTable table) =
      (GraphTables.rowList table).map genericRow := by
  simp only [GenericGraphTables.rowList, GraphTables.rowList, genericTable,
    genericRows, Vector.toList_map]

@[simp] theorem genericTable_tableWords (table : GraphTables.Table) :
    GenericGraphTables.tableWords (genericTable table) = GraphTables.tableWords table := by
  simp only [GenericGraphTables.tableWords, GraphTables.tableWords,
    genericTable_vertices, genericTable_darts, genericTable_rowList, List.flatMap_map,
    genericRow_words]

@[simp] theorem genericTable_tableBits (table : GraphTables.Table) :
    GenericGraphTables.tableBits (genericTable table) = GraphTables.tableBits table := by
  simp only [GenericGraphTables.tableBits, GraphTables.tableBits, genericTable_tableWords]

@[simp] theorem genericTable_semantics_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).tail e =
      (GraphTables.semantics table).tail e := genericTable_tail table e

@[simp] theorem genericTable_semantics_reverse (table : GraphTables.Table)
    (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).reverse e =
      (GraphTables.semantics table).reverse e := genericTable_reverseIndex table e

@[simp] theorem genericTable_semantics_head (table : GraphTables.Table) (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).head e =
      (GraphTables.semantics table).head e := by
  simp only [ConstraintGraph.head, genericTable_semantics_reverse, genericTable_semantics_tail]
  rfl

@[simp] theorem genericTable_semantics_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (a b : Fin 64) :
    (GenericGraphTables.semantics (genericTable table)).accepts e a b =
      (GraphTables.semantics table).accepts e a b := genericRows_acceptsAt _ _ _ _

@[simp] theorem genericTable_headIndex (table : GraphTables.Table) (e : Fin table.darts) :
    AlphabetTable.Lookup.headIndex (genericTable table) e = table.rows[e].reverseIndex :=
  genericTable_reverseIndex table e

@[simp] theorem genericTable_headValue (table : GraphTables.Table) (e : Fin table.darts) :
    AlphabetTable.Lookup.headValue (genericTable table) e =
      ((GraphTables.semantics table).head e).val := by
  exact (AlphabetTable.Lookup.headValue_eq_semantics (genericTable table) e).trans
    (congrArg Fin.val (genericTable_semantics_head table e))

theorem genericTable_headValue_tableGraph (table : GraphTables.Table) (e : Fin table.darts) :
    AlphabetTable.Lookup.headValue (genericTable table) e =
      ((FinalCNFPattern.tableGraph table).head e).val := by
  rw [genericTable_headValue]
  rfl

theorem genericTable_pattern_relation (table : GraphTables.Table) (e : Fin table.darts)
    (p : VerifierToCNF.PatternIndex 12) :
    (genericTable table).rows[e].relation[FinalCNFPattern.patternRelationIndex p] =
      (FinalCNFPattern.tableVerifier table).accepts e (VerifierToCNF.patternAt 12 p) := by
  rw [genericTable_relation]
  exact FinalCNFPattern.pattern_lookup_eq_verifier_accepts table e p

end DFVSGames.Foundations.Complexity.FinalCNFTableAdapter
end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

@[simp] theorem headRoles_zero : headRoles 0 = Tape.archive := rfl
@[simp] theorem headRoles_one : headRoles 1 = Tape.reverseIndex := rfl
@[simp] theorem headRoles_two : headRoles 2 = Tape.scanWork := rfl
@[simp] theorem headRoles_three : headRoles 3 = Tape.indexWork := rfl
@[simp] theorem headRoles_four : headRoles 4 = Tape.head := rfl
@[simp] theorem headRoles_five : headRoles 5 = Tape.scratch := rfl

def rowOperands (table : GraphTables.Table) (e : Fin table.darts) : Fin 5 → Nat :=
  values table.vertices table.darts table.rows[e].tail.val
    table.rows[table.rows[e].reverseIndex].tail.val e.val

def rowRelation (table : GraphTables.Table) (e : Fin table.darts) : Ambient :=
  ((), fun i => table.rows[e].relation[i])

def rowRest (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) : List Bool :=
  encodeWords (GraphTables.relationWords table.rows[e].relation) ++ rest

def preparedTapes (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  Lookup.headLookupTapes headRoles
    (endpointTapes base table.rows[e].tail.val table.rows[e].reverseIndex.val
      (rowRest table e rest)) (genericTable table) e

theorem prepared_input (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .input = rowRest table e rest := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_head (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .head =
      encodeWord table.rows[table.rows[e].reverseIndex].tail.val := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes,
    genericTable_headValue, GraphTables.semantics, ConstraintGraph.head,
    GraphTables.reverseAt]

theorem prepared_tail (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .tail = encodeWord table.rows[e].tail.val ++ base .tail := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_reverse (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .reverseIndex =
      encodeWord table.rows[e].reverseIndex.val ++ base .reverseIndex := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_frame (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) (tape : Tape)
    (hi : tape ≠ .input) (ht : tape ≠ .tail) (hr : tape ≠ .reverseIndex)
    (hh : tape ≠ .head) (hs : tape ≠ .scanWork) (hx : tape ≠ .indexWork) :
    preparedTapes base table e rest tape = base tape := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes, hi, ht, hr, hh, hs, hx]

def emittedTapes (plan : Plan) (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  Function.update (Function.update (preparedTapes base table e rest) Tape.input rest)
    Tape.accumulator ((plan.flatMap (Emitter.commandBits (rowOperands table e)
      (rowRelation table e))).reverse ++ base .accumulator)

def rowResultTapes (plan : Plan) (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  finishTapes (emittedTapes plan base table e rest) e.val

@[simp] theorem rowResult_input (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .input = rest := by
  simp [rowResultTapes, finishTapes, emittedTapes]

@[simp] theorem rowResult_tail (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .tail = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_head (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .head = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_reverse (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .reverseIndex = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_index (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .rowIndex = encodeWord (e.val + 1) := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_accumulator (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .accumulator =
      (plan.flatMap (Emitter.commandBits (rowOperands table e) (rowRelation table e))).reverse ++
        base .accumulator := by
  simp [rowResultTapes, finishTapes, emittedTapes]

theorem rowResult_frame (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) (tape : Tape)
    (hi : tape ≠ .input) (ht : tape ≠ .tail) (hr : tape ≠ .reverseIndex)
    (hh : tape ≠ .head) (hs : tape ≠ .scanWork) (hx : tape ≠ .indexWork)
    (ha : tape ≠ .accumulator) (hc : tape ≠ .rowIndex) :
    rowResultTapes plan base table e rest tape = base tape := by
  simp only [rowResultTapes, finishTapes, emittedTapes, Function.update_of_ne hi,
    Function.update_of_ne ht, Function.update_of_ne hr, Function.update_of_ne hh,
    Function.update_of_ne ha, Function.update_of_ne hc]
  exact prepared_frame base table e rest tape hi ht hr hh hs hx

def guardRowInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (ambient : Ambient) (hinput : base .input ≠ []) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .guard, ((ambient, ()), none), base⟩
      (some ⟨some .startTail, ((ambient, ()), none), base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .guard) _ _) = _
    cases hb : base .input with
    | nil => exact False.elim (hinput hb)
    | cons b bs => simp [program, guard, TM2.stepAux, hb]
  steps_le_m := Nat.le_refl _

def guardEndInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (ambient : Ambient) (hinput : base .input = []) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .guard, ((ambient, ()), none), base⟩
      (some ⟨some .reverseOutput, ((ambient, ()), none), base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .guard) _ _) = _
    simp [program, guard, TM2.stepAux, hinput]
  steps_le_m := Nat.le_refl _

theorem prepared_operands (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool)
    (hn : base .vertices = encodeWord table.vertices)
    (hm : base .darts = encodeWord table.darts)
    (hr : base .rowIndex = encodeWord e.val)
    (ht : base .tail = []) :
    ∀ i, (Function.update (preparedTapes base table e rest) Tape.input rest) (source i) =
      encodeWord (rowOperands table e i) := by
  intro i
  fin_cases i
  · simpa [source, rowOperands, values] using
      prepared_frame base table e rest .vertices (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) |>.trans hn
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.darts = _
    simp only [Function.update_of_ne (show Tape.darts ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .darts (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hm
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.tail = _
    simp only [Function.update_of_ne (show Tape.tail ≠ Tape.input by decide), prepared_tail,
      ht, List.append_nil]
    rfl
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.head = _
    simp only [Function.update_of_ne (show Tape.head ≠ Tape.input by decide), prepared_head]
    rfl
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.rowIndex = _
    simp only [Function.update_of_ne (show Tape.rowIndex ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .rowIndex (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hr

theorem rowOperands_bounded (table : GraphTables.Table) (e : Fin table.darts) :
    ∀ i, rowOperands table e i ≤ (GraphTables.tableBits table).length := by
  intro i
  fin_cases i
  · exact GraphTables.vertices_le_tableBits_length table
  · exact GraphTables.darts_le_tableBits_length table
  · exact table.rows[e].tail.isLt.le.trans (GraphTables.vertices_le_tableBits_length table)
  · exact table.rows[table.rows[e].reverseIndex].tail.isLt.le.trans
      (GraphTables.vertices_le_tableBits_length table)
  · exact e.isLt.le.trans (GraphTables.darts_le_tableBits_length table)

def rowTime (plan : Plan) (N : Nat) : Nat :=
  plan.length * (3 * (N + 1) + 3) + 12 * N + 15

noncomputable def rowInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool)
    (hinput : base .input = encodeWords (GraphTables.rowWords table.rows[e]) ++ rest)
    (harchive : base .archive = GraphTables.tableBits table)
    (hn : base .vertices = encodeWord table.vertices)
    (hm : base .darts = encodeWord table.darts)
    (hrow : base .rowIndex = encodeWord e.val)
    (ht : base .tail = []) (hh : base .head = []) (hr : base .reverseIndex = [])
    (hscratch : base .scratch = []) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .startTail, ((ambient, ()), none), base⟩
      (some ⟨some .guard, ((rowRelation table e, ()), none),
        rowResultTapes plan base table e rest⟩)
      (rowTime plan (GraphTables.tableBits table).length) := by
  let parsed := endpointTapes base table.rows[e].tail.val table.rows[e].reverseIndex.val
    (rowRest table e rest)
  let ready := preparedTapes base table e rest
  let read := Function.update ready Tape.input rest
  let output := emittedTapes plan base table e rest
  let run₁ := endpointsInTime headerPlan plan base table.rows[e].tail.val
    table.rows[e].reverseIndex.val (rowRest table e rest)
    (by simpa [GraphTables.rowWords, encodeWords, List.append_assoc, rowRest] using hinput) ambient
  have parsed_archive : parsed .archive = GenericGraphTables.tableBits (genericTable table) := by
    simpa [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes] using harchive
  have parsed_reverse : parsed .reverseIndex =
      encodeWord (Lookup.headIndex (genericTable table) e).val := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hr]
  have parsed_head : parsed .head = [] := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hh]
  have parsed_scratch : parsed .scratch = [] := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hscratch]
  let run₂ := headPhaseInTime headerPlan plan parsed (genericTable table) e
    parsed_archive parsed_reverse parsed_head parsed_scratch ambient
  let run₃ := relationInTime headerPlan plan ready table.rows[e].relation rest
    (prepared_input base table e rest) ambient
  have read_operands : ∀ i, read (source i) = encodeWord (rowOperands table e i) :=
    prepared_operands base table e rest hn hm hrow ht
  have read_scratch : read .scratch = [] := by
    simp only [read, Function.update_of_ne (show Tape.scratch ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hscratch
  have read_acc : read .accumulator = base .accumulator := by
    simp only [read, Function.update_of_ne (show Tape.accumulator ≠ Tape.input by decide)]
    exact prepared_frame base table e rest .accumulator (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have run₄ : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((rowRelation table e, ()), none), read⟩
      (some ⟨some .clearTail, ((rowRelation table e, ()), none), output⟩)
      (plan.length * (3 * ((GraphTables.tableBits table).length + 1) + 3) + 1) := by
    simpa only [read_acc, output, emittedTapes, read, ready] using
      emitInTime headerPlan plan read (rowOperands table e) read_operands read_scratch
        (rowRelation table e) (GraphTables.tableBits table).length (rowOperands_bounded table e)
  have output_tail : output .tail = encodeWord table.rows[e].tail.val := by
    simp [output, emittedTapes, prepared_tail, ht]
  have output_head : output .head = encodeWord table.rows[table.rows[e].reverseIndex].tail.val := by
    simp [output, emittedTapes, prepared_head]
  have output_reverse : output .reverseIndex = encodeWord table.rows[e].reverseIndex.val := by
    simp [output, emittedTapes, prepared_reverse, hr]
  have output_row : output .rowIndex = encodeWord e.val := by
    simp only [output, emittedTapes,
      Function.update_of_ne (show Tape.rowIndex ≠ Tape.accumulator by decide),
      Function.update_of_ne (show Tape.rowIndex ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .rowIndex (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hrow
  let run₅ := finishInTime headerPlan plan output table.rows[e].tail.val
    table.rows[table.rows[e].reverseIndex].tail.val table.rows[e].reverseIndex.val e.val
    output_tail output_head output_reverse output_row (rowRelation table e)
  let r₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let r₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂ run₃
  let r₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃ run₄
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃₄ run₅
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have hb := run.steps_le_m
  have htbound := rowOperands_bounded table e 2
  have hhbound := rowOperands_bounded table e 3
  have hrbound := table.rows[e].reverseIndex.isLt.le.trans (GraphTables.darts_le_tableBits_length table)
  change table.rows[e].tail.val ≤ _ at htbound
  change table.rows[table.rows[e].reverseIndex].tail.val ≤ _ at hhbound
  simp only [Lookup.headTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, genericTable_tableBits] at hb
  unfold rowTime
  omega

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program
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
