import OAI.Computability.BinPacking.PCP.Cleanup
import OAI.Computability.BinPacking.PCP.CompareLoop
import OAI.Computability.BinPacking.PCP.Lookup

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Setup

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Foundations.Hastad

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

abbrev Ports (K : Type) := Fin 7 → K

inductive Label
  | copyFirst | copySecond | verticesStart | verticesLoop
  | dartsStart | dartsLoop | counterFirst | counterSecond | initialize
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyFirst, .copySecond, .verticesStart,
  .verticesLoop, .dartsStart, .dartsLoop, .counterFirst, .counterSecond, .initialize]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def statement (ports : Ports K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .copyFirst => Reduction.MachineTransfer.loopAt (ports 0) (ports 5) id false
      (labels .copyFirst) (some (labels .copySecond))
  | .copySecond => MachineCopy.forkLoop (ports 5) (ports 0) (ports 1) false
      (labels .copySecond) (some (labels .verticesStart))
  | .verticesStart => SourceMachine.fieldStart (ports 2) (labels .verticesLoop)
  | .verticesLoop => SourceMachine.fieldLoop (ports 1) (ports 2)
      (labels .verticesLoop) (some (labels .dartsStart))
  | .dartsStart => SourceMachine.fieldStart (ports 3) (labels .dartsLoop)
  | .dartsLoop => SourceMachine.fieldLoop (ports 1) (ports 3)
      (labels .dartsLoop) (some (labels .counterFirst))
  | .counterFirst => Reduction.MachineTransfer.loopAt (ports 3) (ports 5) id false
      (labels .counterFirst) (some (labels .counterSecond))
  | .counterSecond => MachineCopy.forkLoop (ports 5) (ports 3) (ports 4) false
      (labels .counterSecond) (some (labels .initialize))
  | .initialize => .push (ports 6) (fun _ => false)
      (.load (fun state => (state.1, none)) (Reduction.MachineTransfer.exitAt (ports 6) exit))

def resultTapes (ports : Ports K) (base : K → List Bool)
    (n m : Nat) (rows : List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update (Function.update base (ports 1) rows)
          (ports 2) (encodeWord n)) (ports 3) (encodeWord m))
      (ports 4) (encodeWord m)) (ports 6) (encodeWord 0)

theorem resultTapes_other (ports : Ports K) (base : K → List Bool)
    (n m : Nat) (rows : List Bool) (tape : K)
    (h : ∀ i : Fin 7, i ≠ 0 → i ≠ 5 → tape ≠ ports i) :
    resultTapes ports base n m rows tape = base tape := by
  simp [resultTapes, h]

def setupInTime (ports : Ports K) (distinct : Function.Injective ports)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ label, program (labels label) = statement ports labels exit label)
    (base : K → List Bool) (n m : Nat) (rows : List Bool)
    (initial : ∀ i : Fin 7, base (ports i) =
      if i = 0 then encodeWord n ++ (encodeWord m ++ rows) else [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copyFirst), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), resultTapes ports base n m rows⟩)
      (2 * (encodeWord n ++ (encodeWord m ++ rows)).length + n + 3 * m + 11) := by
  let input := encodeWord n ++ (encodeWord m ++ rows)
  let t₀ := Function.update base (ports 1) input
  let t₁ := SourceMachine.afterField (ports 1) (ports 2) t₀ n (encodeWord m ++ rows)
  let t₂ := SourceMachine.afterField (ports 1) (ports 3) t₁ m rows
  let t₃ := Function.update t₂ (ports 4) (encodeWord m)
  have hne {i j : Fin 7} (h : i ≠ j) : ports i ≠ ports j := fun e => h (distinct e)
  have run₀ := MachineCopy.copyInTime (ports 0) (ports 1) (ports 5)
    (hne (by decide)) (hne (by decide)) (hne (by decide)) false
    (labels .copyFirst) (labels .copySecond) (some (labels .verticesStart))
    program (atLabels .copyFirst) (atLabels .copySecond) base
    (by simp [initial]) ambient register
  have hb0 : base (ports 0) = input := by simpa [input] using initial 0
  have hb1 : base (ports 1) = [] := by simpa using initial 1
  rw [hb0, hb1, List.append_nil] at run₀
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (labels .copyFirst), (ambient, register), base⟩
    (some ⟨some (labels .verticesStart), (ambient, none), t₀⟩)
    (2 * (input.length + 1)) at run₀
  have run₁ := SourceMachine.fieldInTime (ports 1) (ports 2) (hne (by decide))
    (labels .verticesStart) (labels .verticesLoop) (some (labels .dartsStart))
    program (atLabels .verticesStart) (atLabels .verticesLoop)
    t₀ n (encodeWord m ++ rows) (by simp [t₀, input]) ambient none
  have run₂ := SourceMachine.fieldInTime (ports 1) (ports 3) (hne (by decide))
    (labels .dartsStart) (labels .dartsLoop) (some (labels .counterFirst))
    program (atLabels .dartsStart) (atLabels .dartsLoop)
    t₁ m rows (by simp [t₁, SourceMachine.afterField, distinct.eq_iff]) ambient none
  have h₂m : t₂ (ports 3) = encodeWord m := by
    simp [t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
      distinct.eq_iff, initial]
  have h₂c : t₂ (ports 4) = [] := by
    simp [t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
      distinct.eq_iff, initial]
  have h₂s : t₂ (ports 5) = [] := by
    simp [t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
      distinct.eq_iff, initial]
  have run₃ := MachineCopy.copyInTime (ports 3) (ports 4) (ports 5)
    (hne (by decide)) (hne (by decide)) (hne (by decide)) false
    (labels .counterFirst) (labels .counterSecond) (some (labels .initialize))
    program (atLabels .counterFirst) (atLabels .counterSecond) t₂ h₂s ambient none
  rw [h₂m, h₂c, List.append_nil, encodeWord_length] at run₃
  have h₃e : t₃ (ports 6) = [] := by
    simp [t₃, t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
      distinct.eq_iff, initial]
  have hresult : Function.update t₃ (ports 6) [false] =
      resultTapes ports base n m rows := by
    funext tape
    by_cases h1 : tape = ports 1
    · subst tape; simp [t₃, t₂, t₁, t₀, SourceMachine.afterField,
        SourceMachine.fieldTapes, resultTapes, distinct.eq_iff]
    · by_cases h2 : tape = ports 2
      · subst tape; simp [t₃, t₂, t₁, t₀, SourceMachine.afterField,
          SourceMachine.fieldTapes, resultTapes, distinct.eq_iff, initial]
      · by_cases h3 : tape = ports 3
        · subst tape; simp [t₃, t₂, t₁, t₀, SourceMachine.afterField,
            SourceMachine.fieldTapes, resultTapes, distinct.eq_iff, initial]
        · simp [t₃, t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
            resultTapes, Function.update_apply, h1, h2, h3, encodeWord]
  have run₄ : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .initialize), (ambient, none), t₃⟩
      (some ⟨exit, (ambient, none), resultTapes ports base n m rows⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program (labels .initialize)) (ambient, none) t₃) = _
      rw [atLabels]
      cases exit <;> simp [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt,
        h₃e, hresult]
    steps_le_m := Nat.le_refl _ }
  let r₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₀ run₁
  let r₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₀₁ run₂
  let r₀₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₀₁₂ run₃
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₀₁₂₃ run₄
  exact {
    toEvalsTo := run.toEvalsTo
    steps_le_m := by
      have h := run.steps_le_m
      dsimp [input] at h
      omega }

def tableSetupInTime {q : Nat} (ports : Ports K) (distinct : Function.Injective ports)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ label, program (labels label) = statement ports labels exit label)
    (base : K → List Bool) (table : GenericGraphTables.Table q)
    (initial : ∀ i : Fin 7, base (ports i) =
      if i = 0 then GenericGraphTables.tableBits table else [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copyFirst), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), resultTapes ports base table.vertices table.darts
        (encodeWords ((GenericGraphTables.rowList table).flatMap GenericGraphTables.rowWords))⟩)
      (6 * (GenericGraphTables.tableBits table).length + 11) := by
  have hb := Input.tableBits_header table
  let run := setupInTime ports distinct labels exit program atLabels base
    table.vertices table.darts
    (encodeWords ((GenericGraphTables.rowList table).flatMap GenericGraphTables.rowWords))
    (by intro i; rw [initial i, hb]) ambient register
  have hn := GenericGraphTables.vertices_le_tableBits_length table
  have hm := GenericGraphTables.darts_le_tableBits_length table
  exact {
    toEvalsTo := run.toEvalsTo
    steps_le_m := by
      have h := run.steps_le_m
      have hlen := congrArg List.length hb
      omega }

def program (ports : Ports K) : Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool) :=
  statement ports id none

def machine : FinTM2 where
  K := Fin 7
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label
  main := .copyFirst
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program id

end BinPackingGames.Foundations.PCP.AlphabetTable.Setup

namespace BinPackingGames.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open BinPackingGames.Foundations.Complexity
open Emitter

abbrev Context (q : Nat) := Vector Bool (q * q) × Bool
abbrev RowCommand (q : Nat) := Command 5 (Context q) (Addresses.fieldBound q)

def relationBits (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : List (Context q → Bool) :=
  List.ofFn fun index : Fin 4096 => fun context =>
    (Relations.relationFromTable context.1 context.2 event slot orientation)[index]

private theorem vector_list_ofFn {α : Type} {n : Nat} (vector : Vector α n) :
    List.ofFn (fun index : Fin n => vector[index]) = vector.toList := by
  have equality := congrArg Vector.toList (Vector.ofFn_getElem (xs := vector))
  simpa only [Vector.toList_ofFn, Fin.getElem_fin] using equality

private theorem bitValues_ofFn {σ : Type} {n : Nat}
    (relation : σ → Vector Bool n) (context : σ) :
    (List.ofFn (fun index : Fin n => fun state => (relation state)[index])).map
      (fun bit => if bit context then 1 else 0) =
      (relation context).toList.map GraphTables.bitWord := by
  rw [← vector_list_ofFn (relation context)]
  simp only [List.map_ofFn]
  rfl

theorem relationBits_values (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (context : Context q) :
    (relationBits q event slot orientation).map (fun bit => if bit context then 1 else 0) =
      GraphTables.relationWords
        (Relations.relationFromTable context.1 context.2 event slot orientation) := by
  exact bitValues_ofFn (fun state : Context q =>
    Relations.relationFromTable state.1 state.2 event slot orientation) context

def rowCommands (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : List (RowCommand q) :=
  affineCommands (Addresses.dartTailTerms q event slot orientation)
      (fun context => Addresses.dartTailOffset q event slot orientation
        (Relations.oldPredicate context.1)) ++
    affineCommands (Addresses.reverseDartField q event slot orientation).terms
      (fun _ => (Addresses.reverseDartField q event slot orientation).offset) ++
    bitCommands (relationBits q event slot orientation)

def rowContext {q : Nat} (input : GenericGraphTables.Table q) (edge : Fin input.darts) : Context q :=
  let old := input.rows[edge]
  (old.relation, decide (old.tail = input.rows[old.reverseIndex].tail))

def rowValues {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) : Fin 5 → Nat :=
  let old := input.rows[edge]
  Addresses.values input.vertices input.darts edge.val old.tail.val
    input.rows[old.reverseIndex].tail.val

private theorem encodedRow {n m : Nat} (row : GraphTables.DartRow n m) :
    encodeWords (GraphTables.rowWords row) =
      encodeWord row.tail.val ++ (encodeWord row.reverseIndex.val ++
        encodeWords (GraphTables.relationWords row.relation)) := by
  simp only [GraphTables.rowWords, List.cons_append, List.nil_append, encodeWords]

theorem rowCommands_bits {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    (rowCommands q event slot orientation).flatMap
      (commandBits (rowValues input edge) (rowContext input edge)) =
      encodeWords (GraphTables.rowWords
        (Table.rowFromDart input (((edge, event), slot), orientation))) := by
  rw [rowCommands, List.flatMap_append, List.flatMap_append,
    affineCommands_bits, affineCommands_bits, bitCommands_bits, relationBits_values]
  have htail := Addresses.fieldForDartTail_eval input.vertices input.darts q edge
    input.rows[edge].tail input.rows[input.rows[edge].reverseIndex].tail event slot orientation
    (Relations.oldPredicate input.rows[edge].relation)
  have hreverse := Addresses.reverseDartField_eval input.vertices input.darts q edge
    event slot orientation input.rows[edge].tail.val
      input.rows[input.rows[edge].reverseIndex].tail.val
  let row := Table.rowFromDart input (((edge, event), slot), orientation)
  have tailEq : affineValue (Addresses.dartTailTerms q event slot orientation)
      (rowValues input edge) (Addresses.dartTailOffset q event slot orientation
        (Relations.oldPredicate (rowContext input edge).1)).val = row.tail.val := htail
  have reverseEq : affineValue (Addresses.reverseDartField q event slot orientation).terms
      (rowValues input edge) (Addresses.reverseDartField q event slot orientation).offset.val =
      row.reverseIndex.val := hreverse
  have relationEq : Relations.relationFromTable (rowContext input edge).1
      (rowContext input edge).2 event slot orientation = row.relation := rfl
  rw [encodedRow]
  have combined := congrArg₂ (fun a b : List Bool => a ++ b)
    (congrArg encodeWord tailEq)
    (congrArg₂ (fun a b : List Bool => a ++ b) (congrArg encodeWord reverseEq)
      (congrArg (fun relation => encodeWords (GraphTables.relationWords relation)) relationEq))
  simpa only [List.append_assoc] using combined

def blockCommands (q : Nat) : List (RowCommand q) :=
  (Enumeration.localEvents q).flatMap fun event =>
    (List.finRange 6).flatMap fun slot =>
      [false, true].flatMap fun orientation => rowCommands q event slot orientation

def blockWords {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) : List Nat :=
  (Enumeration.localEvents q).flatMap fun event =>
    (List.finRange 6).flatMap fun slot =>
      [false, true].flatMap fun orientation =>
        GraphTables.rowWords (Table.rowFromDart input (((edge, event), slot), orientation))

theorem tableWords_eq_blocks {q : Nat}
    (input : GenericGraphTables.Table q) :
    GraphTables.tableWords (Table.build input) =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] ++
      (List.finRange input.darts).flatMap (blockWords input) := by
  rw [Table.tableWords_eq_ordered, Enumeration.ordered_dart]
  unfold blockWords
  simp only [List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

def headerCommands (q : Nat) (σ : Type) : List (Command 2 σ (Addresses.fieldBound q)) :=
  affineCommands [(0, Enumeration.tapeCount q),
      (1, Enumeration.localCount q + Enumeration.pairTapeCount q)]
      (fun _ => Addresses.zeroOffset q) ++
    affineCommands [(1, 12 * Enumeration.localCount q)] (fun _ => Addresses.zeroOffset q)

theorem headerCommands_bits {σ : Type} (q n m : Nat) (ambient : σ) :
    (headerCommands q σ).flatMap (commandBits ![n, m] ambient) =
      encodeWords [Enumeration.vertexCount n m q, Enumeration.dartCount m q] := by
  rw [headerCommands, List.flatMap_append, affineCommands_bits, affineCommands_bits]
  have vertices : affineValue
      [(0, Enumeration.tapeCount q), (1, Enumeration.localCount q + Enumeration.pairTapeCount q)]
      ![n, m] (Addresses.zeroOffset q).val = Enumeration.vertexCount n m q := by
    exact Addresses.headerVertices_eval q n m 0 0 0
  have darts : affineValue [(1, 12 * Enumeration.localCount q)] ![n, m]
      (Addresses.zeroOffset q).val = Enumeration.dartCount m q := by
    exact Addresses.headerDarts_eval q n m 0 0 0
  rw [vertices, darts]
  simp [encodeWords]

@[simp] theorem headerCommands_length (q : Nat) (σ : Type) :
    (headerCommands q σ).length = 7 := by
  simp [headerCommands, affineCommands_length]

def headerInTime {K Λ σ : Type} [DecidableEq K] (q n m : Nat)
    (sources : Fin 2 → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label (headerCommands q σ).length (Addresses.fieldBound q) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement (listCommands (headerCommands q σ))
      sources scratch output labels exit label)
    (base : K → List Bool) (operands : ∀ i, base (sources i) = encodeWord (![n, m] i))
    (scratchEmpty : base scratch = []) (ambient : σ) (N : Nat) (hn : n ≤ N) (hm : m ≤ N) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (labelAt (headerCommands q σ).length (Addresses.fieldBound q) 0 .entry)),
        ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes output base
        (encodeWords [Enumeration.vertexCount n m q, Enumeration.dartCount m q])⟩)
      (7 * (3 * (N + 1) + 3) + 1) := by
  have bounded : ∀ i : Fin 2, ![n, m] i ≤ N := by
    intro i
    fin_cases i <;> simp [hn, hm]
  have run := planInTime (listCommands (headerCommands q σ)) sources scratch output
    sourceScratch sourceOutput scratchOutput labels exit p atLabels ![n, m] base operands
    scratchEmpty ambient N bounded
  rw [bits_listCommands, headerCommands_bits] at run
  simpa only [headerCommands_length] using run

private theorem encodeWords_flatMap {α : Type} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [encodeWords_append, ih]

theorem blockCommands_bits {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) :
    (blockCommands q).flatMap (commandBits (rowValues input edge) (rowContext input edge)) =
      encodeWords (blockWords input edge) := by
  simp only [blockCommands, blockWords, List.flatMap_assoc, encodeWords_flatMap,
    rowCommands_bits]

theorem rowCommands_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : (rowCommands q event slot orientation).length ≤ 4104 := by
  have htail := Addresses.dartTailTerms_length_le q event slot orientation
  simp only [rowCommands, List.length_append, affineCommands_length,
    Addresses.reverseDartField, List.length_cons, List.length_nil,
    bitCommands, List.length_map, relationBits, List.length_ofFn]
  omega

private theorem flatMap_length_le {α β : Type} (items : List α) (f : α → List β)
    (bound : Nat) (bounded : ∀ item ∈ items, (f item).length ≤ bound) :
    (items.flatMap f).length ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item items ih =>
    have hh := bounded item (by simp)
    have ht := ih (fun x hx => bounded x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

theorem blockCommands_length_le (q : Nat) :
    (blockCommands q).length ≤ Enumeration.localCount q * (6 * (2 * 4104)) := by
  unfold blockCommands
  apply le_trans (flatMap_length_le _ _ (6 * (2 * 4104)) ?_) (by simp)
  intro event _
  apply le_trans (flatMap_length_le _ _ (2 * 4104) ?_) (by simp)
  intro slot _
  apply le_trans (flatMap_length_le _ _ 4104 ?_) (by simp)
  intro orientation _
  exact rowCommands_length_le q event slot orientation

def blockInTime {K Λ : Type} [DecidableEq K] {q : Nat}
    (input : GenericGraphTables.Table q) (edge : Fin input.darts)
    (sources : Fin 5 → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label (blockCommands q).length (Addresses.fieldBound q) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State (Context q)))
    (atLabels : ∀ label, p (labels label) = statement (listCommands (blockCommands q))
      sources scratch output labels exit label)
    (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (rowValues input edge i))
    (scratchEmpty : base scratch = []) (N : Nat)
    (bounded : ∀ i, rowValues input edge i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (labelAt (blockCommands q).length (Addresses.fieldBound q) 0 .entry)),
        ((rowContext input edge, ()), none), base⟩
      (some ⟨exit, ((rowContext input edge, ()), none),
        resultTapes output base (encodeWords (blockWords input edge))⟩)
      (Enumeration.localCount q * (6 * (2 * 4104)) * (3 * (N + 1) + 3) + 1) := by
  let run := planInTime (listCommands (blockCommands q)) sources scratch output sourceScratch
    sourceOutput scratchOutput labels exit p atLabels (rowValues input edge) base operands
    scratchEmpty (rowContext input edge) N bounded
  have hbits := bits_listCommands (blockCommands q) (rowValues input edge) (rowContext input edge)
  rw [blockCommands_bits] at hbits
  rw [hbits] at run
  exact { toEvalsTo := run.toEvalsTo, steps_le_m :=
    run.steps_le_m.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (blockCommands_length_le q)) 1) }

def blockCommandsIn {σ : Type} (q : Nat) (context : σ → Context q) :
    List (Command 5 σ (Addresses.fieldBound q)) :=
  (blockCommands q).map (fun command => command.mapAmbient context)

theorem blockCommandsIn_bits {σ : Type} {q : Nat}
    (input : GenericGraphTables.Table q) (edge : Fin input.darts)
    (context : σ → Context q) (ambient : σ) (hcontext : context ambient = rowContext input edge) :
    (blockCommandsIn q context).flatMap (commandBits (rowValues input edge) ambient) =
      encodeWords (blockWords input edge) := by
  simp only [blockCommandsIn, List.flatMap_map, commandBits_mapAmbient]
  rw [hcontext]
  exact blockCommands_bits input edge

def blockInTimeAmbient {K Λ σ : Type} [DecidableEq K] {q : Nat}
    (input : GenericGraphTables.Table q) (edge : Fin input.darts)
    (context : σ → Context q) (ambient : σ) (hcontext : context ambient = rowContext input edge)
    (sources : Fin 5 → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label (blockCommandsIn q context).length (Addresses.fieldBound q) → Λ)
    (exit : Option Λ) (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement (listCommands (blockCommandsIn q context))
      sources scratch output labels exit label)
    (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (rowValues input edge i))
    (scratchEmpty : base scratch = []) (N : Nat)
    (bounded : ∀ i, rowValues input edge i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (labelAt (blockCommandsIn q context).length (Addresses.fieldBound q) 0 .entry)),
        ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes output base (encodeWords (blockWords input edge))⟩)
      (Enumeration.localCount q * (6 * (2 * 4104)) * (3 * (N + 1) + 3) + 1) := by
  have run := planInTime (listCommands (blockCommandsIn q context)) sources scratch output
    sourceScratch sourceOutput scratchOutput labels exit p atLabels (rowValues input edge)
    base operands scratchEmpty ambient N bounded
  rw [bits_listCommands, blockCommandsIn_bits input edge context ambient hcontext] at run
  have lengthBound : (blockCommandsIn q context).length ≤
      Enumeration.localCount q * (6 * (2 * 4104)) := by
    simpa only [blockCommandsIn, List.length_map] using blockCommands_length_le q
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  exact run.steps_le_m.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ lengthBound) 1)

end BinPackingGames.Foundations.PCP.AlphabetTable.EmitRows

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Driver

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Foundations.Hastad
open RuntimeModel

def headerPlan (q : Nat) := EmitRows.headerCommands q (Ambient q)
def rowPlan (q : Nat) := EmitRows.blockCommandsIn q (@context q)

inductive Label (q : Nat)
  | setup (label : Setup.Label)
  | header (label : Emitter.Label (headerPlan q).length (Addresses.fieldBound q))
  | guard | tailStart | tailLoop | reverseStart | reverseLoop | readPredicate
  | headCopyFirst | headCopySecond | indexCopyFirst | indexCopySecond
  | headVertices | headDarts | headLookup (label : Lookup.Label)
  | compare (label : CompareLoop.Label)
  | emit (label : Emitter.Label (rowPlan q).length (Addresses.fieldBound q))
  | clearField (slot : Fin 3)
  | increment | reverseOutput | cleanup (slot : Fin 16)
  deriving DecidableEq, Fintype

def headerEntry (q : Nat) : Label q :=
  .header (Emitter.labelAt (headerPlan q).length (Addresses.fieldBound q) 0 .entry)

def rowEntry (q : Nat) : Label q :=
  .emit (Emitter.labelAt (rowPlan q).length (Addresses.fieldBound q) 0 .entry)

def clearNext {q : Nat} (slot : Fin 3) : Label q :=
  if h : slot.val < 2 then .clearField ⟨slot.val + 1, by omega⟩ else .increment

def program (q : Nat) : Label q → TM2.Stmt Alphabet (Label q) (State q)
  | .setup label => Setup.statement setupPorts Label.setup (some (headerEntry q)) label
  | .header label => emitterStatement
      (Emitter.statement (Emitter.listCommands (headerPlan q)) headerSources .scratch .reversed
        Label.header (some .guard) label)
  | .guard => MachineUnaryCounter.guard .counter .tailStart .reverseOutput
  | .tailStart => SourceMachine.fieldStart .tail .tailLoop
  | .tailLoop => SourceMachine.fieldLoop .cursor .tail .tailLoop (some .reverseStart)
  | .reverseStart => SourceMachine.fieldStart .reverseIndex .reverseLoop
  | .reverseLoop => SourceMachine.fieldLoop .cursor .reverseIndex .reverseLoop (some .readPredicate)
  | .readPredicate => ReadRelation.parser .cursor .headCopyFirst
  | .headCopyFirst => Reduction.MachineTransfer.loopAt .original .scratch id false
      .headCopyFirst (some .headCopySecond)
  | .headCopySecond => MachineCopy.forkLoop .scratch .original .scan false
      .headCopySecond (some .indexCopyFirst)
  | .indexCopyFirst => Reduction.MachineTransfer.loopAt .reverseIndex .scratch id false
      .indexCopyFirst (some .indexCopySecond)
  | .indexCopySecond => MachineCopy.forkLoop .scratch .reverseIndex .indexScan false
      .indexCopySecond (some .headVertices)
  | .headVertices => MachineLookup.discard .scan .headVertices .headDarts
  | .headDarts => MachineLookup.discard .scan .headDarts (.headLookup .guard)
  | .headLookup label => Lookup.statement q .indexScan .scan .head Label.headLookup
      (some (.compare .leftFirst)) label
  | .compare label => CompareLoop.statement Label.compare (rowEntry q) label
  | .emit label => emitterStatement
      (Emitter.statement (Emitter.listCommands (rowPlan q)) rowSources .scratch .reversed
        Label.emit (some (.clearField 0)) label)
  | .clearField slot => MachineDrain.drain (fieldPorts slot) (.clearField slot)
      (some (clearNext slot))
  | .increment => nextRow .guard
  | .reverseOutput => Reduction.MachineTransfer.loopAt .reversed .output id false
      .reverseOutput (some (.cleanup 0))
  | .cleanup slot => Cleanup.instruction cleanupPorts Label.cleanup (initial q).1 none slot

def machine (q : Nat) : FinTM2 := by
  letI := ReadRelation.stateFintype Flags q
  exact {
    K := Tape
    k₀ := .original
    k₁ := .output
    Γ := Alphabet
    Λ := Label q
    main := .setup .copyFirst
    σ := State q
    initialState := initial q
    m := program q }

@[simp] theorem program_setup (q : Nat) (label : Setup.Label) :
    program q (.setup label) =
      Setup.statement setupPorts Label.setup (some (headerEntry q)) label := rfl

@[simp] theorem program_guard (q : Nat) : program q .guard =
    MachineUnaryCounter.guard .counter .tailStart .reverseOutput := rfl

@[simp] theorem program_headLookup (q : Nat) (label : Lookup.Label) :
    program q (.headLookup label) = Lookup.statement q .indexScan .scan .head
      Label.headLookup (some (.compare .leftFirst)) label := rfl

@[simp] theorem program_compare (q : Nat) (label : CompareLoop.Label) :
    program q (.compare label) = CompareLoop.statement Label.compare (rowEntry q) label := rfl

@[simp] theorem program_increment (q : Nat) : program q .increment = nextRow .guard := rfl

end BinPackingGames.Foundations.PCP.AlphabetTable.Driver

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Initialization

open Turing
open BinPackingGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def inputTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | _ => []

def rowsBits (input : GenericGraphTables.Table q) : List Bool :=
  encodeWords ((GenericGraphTables.rowList input).flatMap GenericGraphTables.rowWords)

def headerBits (input : GenericGraphTables.Table q) : List Bool :=
  encodeWords [Enumeration.vertexCount input.vertices input.darts q,
    Enumeration.dartCount input.darts q]

def setupTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | .cursor => rowsBits input
  | .vertices => encodeWord input.vertices
  | .darts | .counter => encodeWord input.darts
  | .edge => encodeWord 0
  | _ => []

def loopTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | .cursor => rowsBits input
  | .vertices => encodeWord input.vertices
  | .darts | .counter => encodeWord input.darts
  | .edge => encodeWord 0
  | .reversed => (headerBits input).reverse
  | _ => []

def loopStart (input : GenericGraphTables.Table q) :
    TM2.Cfg Alphabet (Driver.Label q) (State q) :=
  ⟨some .guard, initial q, loopTapes input⟩

theorem setupResult_eq (input : GenericGraphTables.Table q) :
    Setup.resultTapes setupPorts (inputTapes input) input.vertices input.darts (rowsBits input) =
      setupTapes input := by
  funext tape
  cases tape <;> simp [Setup.resultTapes, setupPorts, inputTapes, setupTapes]

theorem headerResult_eq (input : GenericGraphTables.Table q) :
    Emitter.resultTapes Tape.reversed (setupTapes input) (headerBits input) = loopTapes input := by
  funext tape
  cases tape <;> simp [Emitter.resultTapes, setupTapes, loopTapes]

theorem machineInitial_eq (input : GenericGraphTables.Table q) :
    initList (Driver.machine q) (GenericGraphTables.tableBits input) =
      (⟨some (.setup .copyFirst), initial q, inputTapes input⟩ :
        TM2.Cfg Alphabet (Driver.Label q) (State q)) := by
  change (⟨some (.setup .copyFirst), initial q, _⟩ :
    TM2.Cfg Alphabet (Driver.Label q) (State q)) = _
  congr 1
  funext tape
  cases tape <;> rfl

def setupInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩)
      (6 * (GenericGraphTables.tableBits input).length + 11) := by
  have initialized : ∀ i : Fin 7, inputTapes input (setupPorts i) =
      if i = 0 then GenericGraphTables.tableBits input else [] := by
    intro i
    fin_cases i <;> rfl
  have run := Setup.tableSetupInTime setupPorts setupPorts_injective Driver.Label.setup
    (some (Driver.headerEntry q)) (Driver.program q) (Driver.program_setup q)
    (inputTapes input) input initialized (initial q).1 none
  have initialState : ((initial q).1, (none : Option Bool)) = initial q := rfl
  have result := setupResult_eq input
  unfold rowsBits at result
  rw [initialState, result] at run
  rw [machineInitial_eq]
  exact run

private theorem headerView_at (label : Emitter.Label (Driver.headerPlan q).length
    (Addresses.fieldBound q)) :
    (MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
      (Driver.program q)) (.header label) =
      Emitter.statement (Emitter.listCommands (Driver.headerPlan q)) headerSources
        Tape.scratch Tape.reversed Driver.Label.header (some .guard) label := by
  change MachineControl.statement id (emitterEquiv q).symm
    (MachineControl.statement id (emitterEquiv q) _) = _
  exact MachineFieldProfile.statement_roundtrip (emitterEquiv q).symm _

def headerInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩
      (some (loopStart input))
      (7 * (3 * ((GenericGraphTables.tableBits input).length + 1) + 3) + 1) := by
  let view := MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
    (Driver.program q)
  have sourceScratch : ∀ i : Fin 2, headerSources i ≠ Tape.scratch := by
    intro i
    fin_cases i <;> decide
  have sourceOutput : ∀ i : Fin 2, headerSources i ≠ Tape.reversed := by
    intro i
    fin_cases i <;> decide
  have operands : ∀ i : Fin 2, setupTapes input (headerSources i) =
      encodeWord (![input.vertices, input.darts] i) := by
    intro i
    fin_cases i <;> rfl
  have run := EmitRows.headerInTime q input.vertices input.darts headerSources
    Tape.scratch Tape.reversed sourceScratch sourceOutput (by decide)
    Driver.Label.header (some .guard) view headerView_at
    (setupTapes input) operands (by rfl) (initial q).1
    (GenericGraphTables.tableBits input).length
    (GenericGraphTables.vertices_le_tableBits_length input)
    (GenericGraphTables.darts_le_tableBits_length input)
  have restored : MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q) view =
      Driver.program q := by
    funext label
    exact MachineFieldProfile.statement_roundtrip (emitterEquiv q) (Driver.program q label)
  have transported := transportInTime (emitterEquiv q) view run
  rw [restored] at transported
  change StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩
    (some ⟨some .guard, initial q,
      Emitter.resultTapes Tape.reversed (setupTapes input) (headerBits input)⟩)
    (7 * (3 * ((GenericGraphTables.tableBits input).length + 1) + 3) + 1) at transported
  rw [headerResult_eq] at transported
  exact transported

def time (N : Nat) : Nat := (6 * N + 11) + (7 * (3 * (N + 1) + 3) + 1)

theorem time_eq (N : Nat) : time N = 27 * N + 54 := by
  unfold time
  omega

def initializeInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some (loopStart input)) (time (GenericGraphTables.tableBits input).length) := by
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (setupInTime input) (headerInTime input)
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have bound := run.steps_le_m
  unfold time
  omega

end BinPackingGames.Foundations.PCP.AlphabetTable.Initialization

end OAI
