import Mathlib
import OAI.Computability.MinUncut.PCP.PoweringOpinionTables

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Input

open MinUncutGames.Foundations.Complexity

export GenericGraphTables (Label RelationTable DartRow Rows Valid Table
  relationIndex relationIndex_val relationAt relationOf relationAt_relationOf
  reverseAt acceptsAt rowList rowList_length semantics semantics_reverse
  semantics_tail semantics_accepts ofGraph semantics_ofGraph ofEnumeratedGraph
  bitWord relationWords relationWords_length rowWords rowWords_length
  rowsWords_length tableWords tableWords_length tableBits encoding
  parseRelation parseRow parseRows decodeTableWords decodeTableBits
  parseRelation_encoded parseRow_encoded parseRows_encoded
  decodeTableWords_encoded decodeTableBits_encoded tableBits_injective
  relationBits_length_le rowBits_length_le rowsBits_length_le tableWords_length_le_bits
  tableBits_length_le vertices_le_tableBits_length darts_le_tableBits_length)

variable {q n m : Nat}

abbrev rowWidth (q : Nat) : Nat := q * q + 2

def rowOffset (q e : Nat) : Nat := 2 + rowWidth q * e

theorem rowsWords_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) :
    rows.flatMap rowWords = (rows.take e).flatMap rowWords ++
      (rowWords rows[e] ++ (rows.drop (e + 1)).flatMap rowWords) := by
  have hs : rows.take e ++ rows[e] :: rows.drop (e + 1) = rows := by
    rw [List.getElem_cons_drop he, List.take_append_drop]
  have hw := congrArg (fun rs : List (DartRow q n m) => rs.flatMap rowWords) hs
  simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc] using hw.symm

theorem rowsBits_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) :
    encodeWords (rows.flatMap rowWords) =
      encodeWords ((rows.take e).flatMap rowWords) ++
        (encodeWords (rowWords rows[e]) ++
          encodeWords ((rows.drop (e + 1)).flatMap rowWords)) := by
  rw [rowsWords_split rows e he]
  simp only [encodeWords_append]

theorem rowsBits_append_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) (suffix : List Bool) :
    encodeWords (rows.flatMap rowWords) ++ suffix =
      encodeWords ((rows.take e).flatMap rowWords) ++
        (encodeWords (rowWords rows[e]) ++
          (encodeWords ((rows.drop (e + 1)).flatMap rowWords) ++ suffix)) := by
  rw [rowsBits_split rows e he]
  simp only [List.append_assoc]

def prefixWords (table : Table q) (e : Fin table.darts) : List Nat :=
  [table.vertices, table.darts] ++ ((rowList table).take e.val).flatMap rowWords

def suffixWords (table : Table q) (e : Fin table.darts) : List Nat :=
  ((rowList table).drop (e.val + 1)).flatMap rowWords

theorem prefixWords_length (table : Table q) (e : Fin table.darts) :
    (prefixWords table e).length = rowOffset q e.val := by
  simp [prefixWords, rowOffset, rowWidth, Nat.mul_comm, Nat.add_comm]
  omega

theorem tableWords_at_row (table : Table q) (e : Fin table.darts) :
    tableWords table = prefixWords table e ++
      (rowWords table.rows[e] ++ suffixWords table e) := by
  have hs := rowsWords_split (rowList table) e.val (by simpa only [rowList_length] using e.isLt)
  simp only [rowList, Vector.getElem_toList] at hs
  unfold tableWords prefixWords suffixWords rowList
  rw [hs]
  simp only [List.append_assoc, Fin.getElem_fin]

theorem tableBits_at_row (table : Table q) (e : Fin table.darts) :
    tableBits table = encodeWords (prefixWords table e) ++
      (encodeWords (rowWords table.rows[e]) ++ encodeWords (suffixWords table e)) := by
  rw [tableBits, tableWords_at_row table e]
  simp only [encodeWords_append]

theorem tableBits_header (table : Table q) :
    tableBits table = encodeWord table.vertices ++
      (encodeWord table.darts ++ encodeWords ((rowList table).flatMap rowWords)) := by
  simp [tableBits, tableWords, encodeWords]

theorem tableWords_drop_row (table : Table q) (e : Fin table.darts) :
    (tableWords table).drop (rowOffset q e.val) =
      rowWords table.rows[e] ++ suffixWords table e := by
  rw [tableWords_at_row table e]
  exact List.drop_left' (l₂ := rowWords table.rows[e] ++ suffixWords table e)
    (prefixWords_length table e)

theorem tableWords_take_row (table : Table q) (e : Fin table.darts) :
    ((tableWords table).drop (rowOffset q e.val)).take (rowWidth q) =
      rowWords table.rows[e] := by
  rw [tableWords_drop_row]
  exact List.take_left' (l₂ := suffixWords table e) (rowWords_length table.rows[e])

theorem tableWords_get_tail (table : Table q) (e : Fin table.darts) :
    (tableWords table)[rowOffset q e.val]? = some table.rows[e].tail.val := by
  have h := congrArg (fun words : List Nat => words[0]?) (tableWords_drop_row table e)
  simpa [List.getElem?_drop, rowWords] using h

theorem tableWords_get_reverse (table : Table q) (e : Fin table.darts) :
    (tableWords table)[rowOffset q e.val + 1]? = some table.rows[e].reverseIndex.val := by
  have h := congrArg (fun words : List Nat => words[1]?) (tableWords_drop_row table e)
  simpa [List.getElem?_drop, rowWords] using h

theorem tableWords_drop_relation (table : Table q) (e : Fin table.darts) :
    (tableWords table).drop (rowOffset q e.val + 2) =
      relationWords table.rows[e].relation ++ suffixWords table e := by
  rw [← List.drop_drop, tableWords_drop_row]
  simp [rowWords]

theorem relationWords_get (relation : RelationTable q) (j : Fin (q * q)) :
    (relationWords relation)[j.val]? = some (bitWord relation[j]) := by
  rw [List.getElem?_eq_getElem (by simpa only [relationWords_length] using j.isLt)]
  simp [relationWords]

theorem tableWords_get_relation (table : Table q) (e : Fin table.darts)
    (j : Fin (q * q)) :
    (tableWords table)[rowOffset q e.val + 2 + j.val]? =
      some (bitWord table.rows[e].relation[j]) := by
  have h := congrArg (fun words : List Nat => words[j.val]?)
    (tableWords_drop_relation table e)
  rw [List.getElem?_drop,
    List.getElem?_append_left (by simpa only [relationWords_length] using j.isLt), relationWords_get] at h
  exact h

theorem tableWords_get_predicate (table : Table q) (e : Fin table.darts)
    (a b : Label q) :
    (tableWords table)[rowOffset q e.val + 2 + (b.val + q * a.val)]? =
      some (bitWord ((semantics table).accepts e a b)) := by
  simpa only [relationIndex_val, semantics_accepts, relationAt] using
    tableWords_get_relation table e ((relationIndex q) (a, b))

theorem rowOffset_lt_length (table : Table q) (e : Fin table.darts) :
    rowOffset q e.val < (tableWords table).length := by
  rw [tableWords_length]
  have h := Nat.mul_le_mul_left (rowWidth q) (Nat.succ_le_of_lt e.isLt)
  rw [Nat.mul_succ] at h
  unfold rowOffset rowWidth at *
  omega

theorem relationOffset_lt_length (table : Table q) (e : Fin table.darts)
    (j : Fin (q * q)) :
    rowOffset q e.val + 2 + j.val < (tableWords table).length := by
  rw [tableWords_length]
  have h := Nat.mul_le_mul_left (rowWidth q) (Nat.succ_le_of_lt e.isLt)
  rw [Nat.mul_succ] at h
  have hj := j.isLt
  unfold rowOffset rowWidth at *
  omega

end MinUncutGames.Foundations.PCP.AlphabetTable.Input

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Setup

open Turing
open MinUncutGames.Foundations.Complexity
open MinUncutGames.Foundations.Hastad

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

end MinUncutGames.Foundations.PCP.AlphabetTable.Setup

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.ReadRelation

open Turing
open MinUncutGames.Foundations.Complexity
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

end MinUncutGames.Foundations.PCP.AlphabetTable.ReadRelation

end
section
namespace MinUncutGames.Foundations.Complexity.MachineLookupSpec

def skipWord : List Bool → List Bool
  | [] => []
  | true :: bs => skipWord bs
  | false :: bs => bs

@[simp] theorem skipWord_encodeWord (n : Nat) (bs : List Bool) :
    skipWord (encodeWord n ++ bs) = bs := by
  induction n with
  | zero => simp [encodeWord, skipWord]
  | succ n ih =>
    simpa [encodeWord, List.replicate_succ, skipWord] using ih

theorem skipWord_iterate_encodeWords (i : Nat) (values : List Nat) :
    (skipWord^[i]) (encodeWords values) = encodeWords (values.drop i) := by
  induction i generalizing values with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases values with
    | nil => simpa [encodeWords, skipWord] using ih []
    | cons n ns =>
      simpa only [encodeWords, skipWord_encodeWord, List.drop_succ_cons] using ih ns

def headWord : List Bool → Option (List Bool)
  | [] => none
  | false :: _ => some [false]
  | true :: bs => (headWord bs).map (true :: ·)

@[simp] theorem headWord_encodeWord (n : Nat) (bs : List Bool) :
    headWord (encodeWord n ++ bs) = some (encodeWord n) := by
  induction n with
  | zero => simp [encodeWord, headWord]
  | succ n ih =>
    simpa [encodeWord, List.replicate_succ, headWord] using
      congrArg (Option.map (true :: ·)) ih

@[simp] theorem headWord_encodeWords (values : List Nat) :
    headWord (encodeWords values) = values.head?.map encodeWord := by
  cases values with
  | nil => rfl
  | cons n ns => exact headWord_encodeWord n (encodeWords ns)

def lookupBits (i : Nat) (table : List Bool) : Option (List Bool) :=
  headWord ((skipWord^[i]) table)

@[simp] theorem lookupBits_encodeWords (i : Nat) (values : List Nat) :
    lookupBits i (encodeWords values) = values[i]?.map encodeWord := by
  rw [lookupBits, skipWord_iterate_encodeWords, headWord_encodeWords,
    List.head?_drop]

def lookupEncoded (index table : List Bool) : Option (List Bool) :=
  match decodeWords index with
  | some [i] => lookupBits i table
  | _ => none

@[simp] theorem decodeWords_encodeWord (i : Nat) :
    decodeWords (encodeWord i) = some [i] := by
  simpa [encodeWords] using decodeWords_encodeWords [i]

@[simp] theorem lookupEncoded_encode (i : Nat) (values : List Nat) :
    lookupEncoded (encodeWord i) (encodeWords values) =
      values[i]?.map encodeWord := by
  simp [lookupEncoded]

theorem lookupEncoded_some (i value : Nat) (values : List Nat)
    (h : values[i]? = some value) :
    lookupEncoded (encodeWord i) (encodeWords values) = some (encodeWord value) := by
  simp [h]

theorem lookupEncoded_none (i : Nat) (values : List Nat)
    (h : values.length ≤ i) :
    lookupEncoded (encodeWord i) (encodeWords values) = none := by
  simp [List.getElem?_eq_none h]

theorem encoded_selected_split (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    encodeWords values = encodeWords (values.take i) ++ encodeWord value ++
      encodeWords (values.drop (i + 1)) := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  have hs : values = values.take i ++ value :: values.drop (i + 1) := by
    calc
      values = values.take i ++ values.drop i := (List.take_append_drop i values).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hi, hv]
  simpa only [encodeWords_append, encodeWords, List.append_assoc] using
    congrArg encodeWords hs

def scannedBits (values : List Nat) (i : Nat) : Nat :=
  (encodeWords (values.take (i + 1))).length

theorem encoded_prefix_length_le (values : List Nat) (i : Nat) :
    (encodeWords (values.take i)).length ≤ (encodeWords values).length := by
  have hs : encodeWords (values.take i) ++ encodeWords (values.drop i) =
      encodeWords values := by
    rw [← encodeWords_append, List.take_append_drop]
  have hl := congrArg List.length hs
  simp only [List.length_append] at hl
  omega

theorem scannedBits_le (values : List Nat) (i : Nat) :
    scannedBits values i ≤ (encodeWords values).length :=
  encoded_prefix_length_le values (i + 1)

theorem scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    scannedBits values i = (encodeWords (values.take i)).length + value + 1 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  simp [scannedBits, List.take_succ_eq_append_getElem hi, hv, encodeWords,
    Nat.add_assoc]

theorem selected_scan_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWords (values.take i)).length + value + 1 ≤
      (encodeWords values).length := by
  rw [← scannedBits_of_some values i value h]
  exact scannedBits_le values i

theorem output_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord value).length ≤ (encodeWords values).length := by
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

theorem index_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord i).length ≤ (encodeWords values).length := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  have hp : i ≤ (encodeWords (values.take i)).length := by
    simp only [encodeWords_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    omega
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

def steps : List Nat → Nat → Nat
  | [], i => 2 * i + 2
  | n :: _, 0 => n + 3
  | n :: ns, i + 1 => n + 2 + steps ns i

theorem steps_le_encoded_length_strong (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * i + 2 := by
  induction values generalizing i with
  | nil => simp [steps, encodeWords]
  | cons n ns ih =>
    cases i with
    | zero =>
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega
    | succ i =>
      have ht := ih i
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega

theorem steps_le_encoded_length (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * i + 3 := by
  have h := steps_le_encoded_length_strong values i
  omega

theorem steps_eq_scannedBits_of_lt (values : List Nat) (i : Nat)
    (h : i < values.length) :
    steps values i = scannedBits values i + i + 2 := by
  induction values generalizing i with
  | nil => simp at h
  | cons n ns ih =>
    cases i with
    | zero => simp [steps, scannedBits, encodeWords, Nat.add_assoc]
    | succ i =>
      have ht := ih i (by simpa using h)
      simp only [scannedBits] at ht
      simp only [steps, scannedBits, List.take_succ_cons, encodeWords,
        List.length_append, encodeWord_length]
      omega

theorem steps_eq_scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    steps values i = scannedBits values i + i + 2 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  exact steps_eq_scannedBits_of_lt values i hi

theorem steps_add_length_of_invalid (values : List Nat) (i : Nat)
    (h : values.length ≤ i) :
    steps values i + values.length = (encodeWords values).length + 2 * i + 2 := by
  induction values generalizing i with
  | nil => simp [steps, encodeWords]
  | cons n ns ih =>
    cases i with
    | zero => simp at h
    | succ i =>
      have ht := ih i (by simpa using h)
      simp only [steps, encodeWords, List.length_append, encodeWord_length,
        List.length_cons]
      omega

theorem steps_le_input_encoding_size (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * (encodeWord i).length := by
  have h := steps_le_encoded_length_strong values i
  rw [encodeWord_length]
  omega

end MinUncutGames.Foundations.Complexity.MachineLookupSpec

end

end OAI
