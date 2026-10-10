import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.TableIteration

namespace OAI

namespace DFVSGames.Foundations.PCP.AlphabetTable.Setup

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

abbrev Ports (K : Type) := Fin 7 → K

inductive Label
  | copyFirst | copySecond | verticesStart | verticesLoop
  | dartsStart | dartsLoop | counterFirst | counterSecond | initialize
  deriving DecidableEq

instance : Fintype Label where
  elems := {.copyFirst, .copySecond, .verticesStart, .verticesLoop,
    .dartsStart, .dartsLoop, .counterFirst, .counterSecond, .initialize}
  complete label := by cases label <;> simp

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

end DFVSGames.Foundations.PCP.AlphabetTable.Setup

namespace DFVSGames.Foundations.PCP.AlphabetTable.ReadRelation

open Turing
open DFVSGames.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) (q : Nat) := (σ × RelationTable q) × Option Bool

def relationEquiv (q : Nat) : RelationTable q ≃ (Fin (q * q) → Bool) where
  toFun relation i := relation[i.val]
  invFun := Vector.ofFn
  left_inv relation := Vector.ofFn_getElem
  right_inv bits := by funext i; simp

@[instance_reducible] def relationFintype (q : Nat) : Fintype (RelationTable q) :=
  Fintype.ofEquiv (Fin (q * q) → Bool) (relationEquiv q).symm

@[instance_reducible] def stateFintype (σ : Type) (q : Nat) [Fintype σ] :
    Fintype (State σ q) := by
  letI := relationFintype q
  exact inferInstance

def readSlot (source : K) (i : Fin (q * q))
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  .pop source
    (fun state head =>
      ((state.1.1, state.1.2.set i.val (head.getD false) i.isLt), head))
    (.branch (fun state => state.2.getD false)
      (.pop source (fun state _ => (state.1, none)) next)
      (.load (fun state => (state.1, none)) next))

theorem stepAux_readSlot (source : K) (i : Fin (q * q)) (bit : Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readSlot source i next) ((ambient, initial), register)
      (Function.update base source (encodeWord (bitWord bit) ++ suffix)) =
      TM2.stepAux next ((ambient, initial.set i.val bit i.isLt), none)
        (Function.update base source suffix) := by
  cases bit <;> simp [readSlot, TM2.stepAux, bitWord, encodeWord]

def readSlots (source : K) : List (Fin (q * q)) →
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) →
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q)
  | [], next => .load (fun state => (state.1, none)) next
  | i :: indices, next => readSlot source i (readSlots source indices next)

def indexedWords (relation : RelationTable q) (indices : List (Fin (q * q))) : List Nat :=
  indices.map (fun i => bitWord relation[i.val])

def fillSlots (relation : RelationTable q) : List (Fin (q * q)) →
    RelationTable q → RelationTable q
  | [], initial => initial
  | i :: indices, initial =>
      fillSlots relation indices (initial.set i.val relation[i.val] i.isLt)

theorem fillSlots_preserves_correct (relation : RelationTable q)
    (indices : List (Fin (q * q))) (initial : RelationTable q) (i : Fin (q * q))
    (hcorrect : initial[i.val] = relation[i.val]) :
    (fillSlots relation indices initial)[i.val] = relation[i.val] := by
  induction indices generalizing initial with
  | nil => exact hcorrect
  | cons j indices ih =>
    apply ih
    by_cases hji : j.val = i.val
    · simp [hji]
    · simp [hji, hcorrect]

theorem fillSlots_mem (relation : RelationTable q) (indices : List (Fin (q * q)))
    (initial : RelationTable q) (i : Fin (q * q)) (hi : i ∈ indices) :
    (fillSlots relation indices initial)[i.val] = relation[i.val] := by
  induction indices generalizing initial with
  | nil => simp at hi
  | cons j indices ih =>
    change (fillSlots relation indices (initial.set j.val relation[j.val] j.isLt))[i.val] = _
    rcases List.mem_cons.mp hi with h | h
    · subst j
      apply fillSlots_preserves_correct
      simp
    · exact ih _ h

theorem fillSlots_finRange (relation initial : RelationTable q) :
    fillSlots relation (List.finRange (q * q)) initial = relation := by
  apply Vector.ext
  intro i hi
  exact fillSlots_mem relation (List.finRange (q * q)) initial ⟨i, hi⟩
    (List.mem_finRange _)

theorem indexedWords_finRange (relation : RelationTable q) :
    indexedWords relation (List.finRange (q * q)) = relationWords relation := by
  have h : (List.finRange (q * q)).map (fun i => relation[i.val]) = relation.toList := by
    rw [List.finRange, List.map_ofFn]
    change List.ofFn (fun i : Fin (q * q) => relation[i.val]) = relation.toList
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
  calc
    _ = ((List.finRange (q * q)).map (fun i => relation[i.val])).map bitWord := by
      simp only [indexedWords, List.map_map, Function.comp_def]
    _ = relation.toList.map bitWord := congrArg (fun bits : List Bool => bits.map bitWord) h
    _ = _ := rfl

theorem stepAux_readSlots (source : K) (indices : List (Fin (q * q)))
    (relation : RelationTable q)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readSlots source indices next) ((ambient, initial), register)
      (Function.update base source (encodeWords (indexedWords relation indices) ++ suffix)) =
      TM2.stepAux next ((ambient, fillSlots relation indices initial), none)
        (Function.update base source suffix) := by
  induction indices generalizing initial register with
  | nil => simp [readSlots, fillSlots, indexedWords, encodeWords, TM2.stepAux]
  | cons i indices ih =>
    simp only [readSlots, indexedWords, List.map_cons, encodeWords, List.append_assoc, fillSlots]
    rw [stepAux_readSlot]
    exact ih _ none

def readRelation (source : K)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  readSlots source (List.finRange (q * q)) next

theorem stepAux_readRelation (source : K) (relation : RelationTable q)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readRelation source next) ((ambient, initial), register)
      (Function.update base source (encodeWords (relationWords relation) ++ suffix)) =
      TM2.stepAux next ((ambient, relation), none) (Function.update base source suffix) := by
  simpa only [readRelation, indexedWords_finRange, fillSlots_finRange] using
    stepAux_readSlots source (List.finRange (q * q)) relation next
      base suffix ambient initial register

theorem stepAux_readRelation_fromTapes (source : K) (relation : RelationTable q)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool)
    (hinput : base source = encodeWords (relationWords relation) ++ suffix)
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readRelation source next) ((ambient, initial), register) base =
      TM2.stepAux next ((ambient, relation), none) (Function.update base source suffix) := by
  have h := stepAux_readRelation source relation next base suffix ambient initial register
  have hbase : Function.update base source (encodeWords (relationWords relation) ++ suffix) =
      base := by rw [← hinput]; exact Function.update_eq_self source base
  rw [hbase] at h
  exact h

omit [DecidableEq K] in
theorem readSlots_pushBound (source : K) (indices : List (Fin (q * q)))
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q)) :
    Runtime.statementPushBound (readSlots source indices next) =
      Runtime.statementPushBound next := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    simp only [readSlots, readSlot, Runtime.statementPushBound, ih, max_self]

omit [DecidableEq K] in
theorem readRelation_pushBound (source : K)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q)) :
    Runtime.statementPushBound (readRelation source next) =
      Runtime.statementPushBound next :=
  readSlots_pushBound source (List.finRange (q * q)) next

def parser (source : K) (exitLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  readRelation source (.goto fun _ => exitLabel)

omit [DecidableEq K] in
theorem parser_pushBound (source : K) (exitLabel : Λ) :
    Runtime.statementPushBound (parser (σ := σ) (q := q) source exitLabel) = 0 := by
  rw [parser, readRelation_pushBound]
  rfl

theorem parserStep (source : K) (readLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (atRead : program readLabel = parser source exitLabel)
    (base : K → List Bool) (relation : RelationTable q) (suffix : List Bool)
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    TM2.step program
      ⟨some readLabel, ((ambient, initial), register),
        Function.update base source (encodeWords (relationWords relation) ++ suffix)⟩ =
      some ⟨some exitLabel, ((ambient, relation), none), Function.update base source suffix⟩ := by
  change some (TM2.stepAux (program readLabel) ((ambient, initial), register)
    (Function.update base source (encodeWords (relationWords relation) ++ suffix))) = _
  rw [atRead, parser, stepAux_readRelation]
  rfl

theorem parserTrace (source : K) (readLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (atRead : program readLabel = parser source exitLabel)
    (base : K → List Bool) (relation : RelationTable q) (suffix : List Bool)
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some readLabel, ((ambient, initial), register),
        Function.update base source (encodeWords (relationWords relation) ++ suffix)⟩) =
      some ⟨some exitLabel, ((ambient, relation), none), Function.update base source suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    parserStep source readLabel exitLabel program atRead base relation suffix ambient initial register

def parserInTime (source : K) (readLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (atRead : program readLabel = parser source exitLabel)
    (base : K → List Bool) (relation : RelationTable q) (suffix : List Bool)
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some readLabel, ((ambient, initial), register),
        Function.update base source (encodeWords (relationWords relation) ++ suffix)⟩
      (some ⟨some exitLabel, ((ambient, relation), none), Function.update base source suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    exact parserTrace source readLabel exitLabel program atRead base relation suffix ambient initial register
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.PCP.AlphabetTable.ReadRelation

namespace DFVSGames.Foundations.Complexity.MachineFixedBlockMap

open Turing

abbrev Buffer (N : Nat) := Fin N → Bool

def emptyBuffer (N : Nat) : Buffer N := fun _ => false

section Chains

variable {K Λ σ : Type} {N : Nat}

def readSlots (src : K) : List (Fin N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)
  | [], next => next
  | i :: slots, next =>
      .pop src (fun state head =>
        (state.1, Function.update state.2 i (head.getD false)))
        (readSlots src slots next)

def fill (slots : List (Fin N)) (bits buffer : Buffer N) : Buffer N :=
  slots.foldl (fun buffer i => Function.update buffer i (bits i)) buffer

theorem fill_apply (slots : List (Fin N)) (bits buffer : Buffer N) (i : Fin N) :
    fill slots bits buffer i = if i ∈ slots then bits i else buffer i := by
  induction slots generalizing buffer with
  | nil => simp [fill]
  | cons j slots ih =>
      change fill slots bits (Function.update buffer j (bits j)) i = _
      rw [ih]
      by_cases hm : i ∈ slots
      · simp [hm]
      · by_cases he : i = j <;> simp [hm, he]

@[simp] theorem fill_all (bits buffer : Buffer N) :
    fill (List.ofFn id) bits buffer = bits := by
  funext i
  simp [fill_apply, List.mem_ofFn]

variable [DecidableEq K]

theorem stepAux_readSlots (src : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (ambient : σ) (bits buffer : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) :
    TM2.stepAux (readSlots src slots next) (ambient, buffer)
        (Function.update tapes src (slots.map bits ++ suffix)) =
      TM2.stepAux next (ambient, fill slots bits buffer)
        (Function.update tapes src suffix) := by
  induction slots generalizing buffer tapes with
  | nil => simp [readSlots, fill]
  | cons i slots ih =>
      simpa only [readSlots, List.map_cons, List.cons_append, TM2.stepAux,
        Function.update_self, List.head?_cons, Option.getD_some, List.tail_cons,
        Function.update_idem, fill, List.foldl_cons] using
        ih (Function.update buffer i (bits i)) tapes

theorem stepAux_readAll (src : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.stepAux (readSlots src (List.ofFn id) next) state tapes =
      TM2.stepAux next (state.1, bits) (Function.update tapes src suffix) := by
  have h := stepAux_readSlots src (List.ofFn id) next state.1 bits state.2 tapes suffix
  have hin : Function.update tapes src ((List.ofFn id).map bits ++ suffix) = tapes := by
    simpa only [List.map_ofFn, Function.comp_id, ← hinput] using
      Function.update_eq_self src tapes
  rw [hin, fill_all] at h
  exact h

omit [DecidableEq K] in
theorem statementPushBound_readSlots (src : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    Runtime.statementPushBound (readSlots src slots next) =
      Runtime.statementPushBound next := by
  induction slots with
  | nil => rfl
  | cons i slots ih => exact ih

def writeSlots {M : Nat} (dst : K) (emit : σ → Buffer M) : List (Fin M) →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | [], next => next
  | i :: slots, next => .push dst (fun state => emit state i) (writeSlots dst emit slots next)

theorem stepAux_writeSlots {M : Nat} (dst : K) (emit : σ → Buffer M)
    (slots : List (Fin M)) (next : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (writeSlots dst emit slots next) state tapes =
      TM2.stepAux next state
        (Function.update tapes dst ((slots.map (emit state)).reverse ++ tapes dst)) := by
  induction slots generalizing tapes with
  | nil => simp [writeSlots]
  | cons i slots ih =>
      simp only [writeSlots, TM2.stepAux]
      rw [ih]
      simp only [Function.update_self, Function.update_idem, List.map_cons,
        List.reverse_cons, List.append_assoc, List.singleton_append]

omit [DecidableEq K] in
theorem statementPushBound_writeSlots {M : Nat} (dst : K) (emit : σ → Buffer M)
    (slots : List (Fin M)) (next : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    Runtime.statementPushBound (writeSlots dst emit slots next) =
      slots.length + Runtime.statementPushBound next := by
  induction slots with
  | nil => simp [writeSlots]
  | cons i slots ih =>
      simp only [writeSlots, Runtime.statementPushBound, ih, List.length_cons]
      omega

end Chains

section Block

variable {K Λ σ : Type} {N M : Nat}

def blockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  readSlots src (List.ofFn id)
    (writeSlots dst (fun state => F state.2) (List.ofFn id).reverse
      (.load (fun state => (state.1, emptyBuffer N)) next))

def finishAt (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def blockMapAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  blockStmt src dst F (finishAt exit)

theorem statementPushBound_blockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    Runtime.statementPushBound (blockStmt src dst F next) =
      M + Runtime.statementPushBound next := by
  simp only [blockStmt, statementPushBound_readSlots, statementPushBound_writeSlots,
    Runtime.statementPushBound, List.length_reverse, List.length_ofFn]

theorem statementPushBound_blockMapAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) :
    Runtime.statementPushBound (blockMapAt (σ := σ) src dst F exit) = M := by
  cases exit <;> simp [blockMapAt, statementPushBound_blockStmt, finishAt,
    Runtime.statementPushBound]

variable [DecidableEq K]

theorem stepAux_blockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.stepAux (blockStmt src dst F next) state tapes =
      TM2.stepAux next (state.1, emptyBuffer N)
        (Function.update (Function.update tapes src suffix) dst
          (List.ofFn (F bits) ++ tapes dst)) := by
  unfold blockStmt
  rw [stepAux_readAll src _ state bits tapes suffix hinput, stepAux_writeSlots]
  simp only [List.map_reverse, List.map_ofFn, Function.comp_id, List.reverse_reverse,
    Function.update_of_ne (Ne.symm hne), TM2.stepAux]

theorem stepAux_blockMapAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.stepAux (blockMapAt src dst F exit) state tapes =
      { l := exit, var := (state.1, emptyBuffer N),
        stk := Function.update (Function.update tapes src suffix) dst
          (List.ofFn (F bits) ++ tapes dst) } := by
  rw [blockMapAt, stepAux_blockStmt src dst F _ hne bits suffix state tapes hinput]
  cases exit <;> rfl

theorem step_blockMapAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (label : Λ) (hprogram : program label = blockMapAt src dst F exit)
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.step program { l := some label, var := state, stk := tapes } =
      some { l := exit
             var := (state.1, emptyBuffer N)
             stk := Function.update (Function.update tapes src suffix) dst
               (List.ofFn (F bits) ++ tapes dst) } := by
  simp only [TM2.step, hprogram,
    stepAux_blockMapAt src dst F exit hne bits suffix state tapes hinput]

end Block

def machine {N M : Nat} (F : Buffer N → Buffer M) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit × Buffer N
  initialState := ((), emptyBuffer N)
  m _ := blockMapAt false true F none

theorem machine_statementPushBound {N M : Nat} (F : Buffer N → Buffer M) :
    Runtime.statementPushBound ((machine F).m ()) = M :=
  statementPushBound_blockMapAt false true F none

end DFVSGames.Foundations.Complexity.MachineFixedBlockMap

end OAI
