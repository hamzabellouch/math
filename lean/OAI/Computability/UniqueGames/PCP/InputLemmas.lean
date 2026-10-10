import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.PCP.GenericGraphTables
import OAI.Computability.UniqueGames.PCP.GraphTables

namespace OAI

section

/-!
Serialization boundaries and direct row lookup for the shared executable
fixed-alphabet graph codec. The alphabet is a fixed parameter. Rows remain in
their stored order, including repeated darts and loops. Word offsets are fixed;
bit offsets are represented by actual encoded prefixes because unary fields
have data-dependent lengths. These are data identities, not runtime certificates.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Input

open UniqueGamesTheorem.Foundations.Complexity

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

/-- Offset measured in natural-word fields, including the two header fields. -/
def rowOffset (q e : Nat) : Nat := 2 + rowWidth q * e

/-- Exact decomposition before, at, and after a selected stored row. -/
theorem rowsWords_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) :
    rows.flatMap rowWords = (rows.take e).flatMap rowWords ++
      (rowWords rows[e] ++ (rows.drop (e + 1)).flatMap rowWords) := by
  have hs : rows.take e ++ rows[e] :: rows.drop (e + 1) = rows := by
    rw [List.getElem_cons_drop he, List.take_append_drop]
  have hw := congrArg (fun rs : List (DartRow q n m) => rs.flatMap rowWords) hs
  simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc] using hw.symm

/-- The unary serialization keeps exactly the same row boundaries, with
separate encoded prefixes rather than an assumed constant bit offset. -/
theorem rowsBits_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) :
    encodeWords (rows.flatMap rowWords) =
      encodeWords ((rows.take e).flatMap rowWords) ++
        (encodeWords (rowWords rows[e]) ++
          encodeWords ((rows.drop (e + 1)).flatMap rowWords)) := by
  rw [rowsWords_split rows e he]
  simp only [encodeWords_append]

/-- A selected row can be followed by an arbitrary caller-owned suffix. -/
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

/-- Removing precisely the two encoded header words exposes the stored rows. -/
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

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Input

end

section

/-!
An actual fixed-alphabet TM2 parser for the complete Boolean relation table.
The finite syntax contains one slot reader for each of the `q*q` coordinates.
Each reader consumes `[false]` or `[true,false]`, stores the bit, and clears the
head register. No parser outcome or execution trace is an assumption.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.ReadRelation

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) (q : Nat) := (σ × RelationTable q) × Option Bool

/-- The relation register is a finite tuple of bits, with no unbounded storage. -/
def relationEquiv (q : Nat) : RelationTable q ≃ (Fin (q * q) → Bool) where
  toFun relation i := relation[i.val]
  invFun := Vector.ofFn
  left_inv relation := Vector.ofFn_getElem
  right_inv bits := by funext i; simp

/-- Executable enumeration used when assembling the finite machine state. -/
@[instance_reducible] def relationFintype (q : Nat) : Fintype (RelationTable q) :=
  Fintype.ofEquiv (Fin (q * q) → Bool) (relationEquiv q).symm

@[instance_reducible] def stateFintype (σ : Type) (q : Nat) [Fintype σ] :
    Fintype (State σ q) := by
  letI := relationFintype q
  exact inferInstance

/-- Read one encoded Boolean into a fixed slot of the finite relation register. -/
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

/-- Each stored register bit is obtained from its actual serialized field. -/
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

/-- Fixed finite program fragment; it can be inserted before any continuation. -/
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

/-- One transition executes the fixed chain of `q*q` slot readers. -/
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

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.ReadRelation

end

section

/-!
Concrete bridges between graph cardinality and the length of the validated
unary table encoding. These bounds supply the input-length and intermediate
encoding estimates used by actual machine trace composition; they are not
themselves a machine execution certificate.
-/

namespace UniqueGamesTheorem.Foundations.PCP.GraphTableComplexity

open UniqueGamesTheorem.Foundations.Complexity
open Polynomial

noncomputable def encodingPolynomial (q : Nat) : Polynomial Nat :=
  X ^ 2 + C (2 * (q * q) + 1) * X + C 2

theorem encodingPolynomial_eval (q n : Nat) :
    (encodingPolynomial q).eval n = n ^ 2 + (2 * (q * q) + 1) * n + 2 := by
  simp [encodingPolynomial]

theorem encodingPolynomial_mono (q : Nat) {n m : Nat} (hnm : n ≤ m) :
    (encodingPolynomial q).eval n ≤ (encodingPolynomial q).eval m := by
  rw [encodingPolynomial_eval, encodingPolynomial_eval]
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.pow_le_pow_left hnm 2) (Nat.mul_le_mul_left _ hnm)) 2

theorem rowBound_le_polynomial (q vertices darts : Nat) :
    vertices + darts + 2 + darts * (vertices + darts + 2 * (q * q)) ≤
      (encodingPolynomial q).eval (vertices + darts) := by
  have hd : darts ≤ vertices + darts := Nat.le_add_left darts vertices
  calc
    _ ≤ vertices + darts + 2 +
        (vertices + darts) * (vertices + darts + 2 * (q * q)) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _
    _ = _ := by rw [encodingPolynomial_eval]; ring

theorem generic_size_add_two_le_bits {q : Nat} (table : GenericGraphTables.Table q) :
    table.vertices + table.darts + 2 ≤ (GenericGraphTables.tableBits table).length := by
  simp only [GenericGraphTables.tableBits, GenericGraphTables.tableWords,
    encodeWords_append, List.length_append, encodeWords, encodeWord_length, List.length_nil]
  omega

theorem generic_bits_le_polynomial {q : Nat} (table : GenericGraphTables.Table q) :
    (GenericGraphTables.tableBits table).length ≤
      (encodingPolynomial q).eval (table.vertices + table.darts) :=
  (GenericGraphTables.tableBits_length_le table).trans
    (rowBound_le_polynomial q table.vertices table.darts)

theorem generic_bits_le_of_size_le {q N : Nat} (table : GenericGraphTables.Table q)
    (hsize : table.vertices + table.darts ≤ N) :
    (GenericGraphTables.tableBits table).length ≤ (encodingPolynomial q).eval N :=
  (generic_bits_le_polynomial table).trans (encodingPolynomial_mono q hsize)

theorem size_add_two_le_bits (table : GraphTables.Table) :
    table.vertices + table.darts + 2 ≤ (GraphTables.tableBits table).length := by
  simp only [GraphTables.tableBits, GraphTables.tableWords,
    encodeWords_append, List.length_append, encodeWords, encodeWord_length, List.length_nil]
  omega

theorem bits_le_polynomial (table : GraphTables.Table) :
    (GraphTables.tableBits table).length ≤
      (encodingPolynomial 64).eval (table.vertices + table.darts) :=
  (GraphTables.tableBits_length_le table).trans
    (rowBound_le_polynomial 64 table.vertices table.darts)

theorem bits_le_of_size_le {N : Nat} (table : GraphTables.Table)
    (hsize : table.vertices + table.darts ≤ N) :
    (GraphTables.tableBits table).length ≤ (encodingPolynomial 64).eval N :=
  (bits_le_polynomial table).trans (encodingPolynomial_mono 64 hsize)

end UniqueGamesTheorem.Foundations.PCP.GraphTableComplexity

end

section

/-! Additive smoothing of the actual fair Boolean-tape length law.  This is
the finite-probability input to the lazy-walk amplification argument. -/

namespace UniqueGamesTheorem.Foundations.PCP.LazySmoothing

open scoped BigOperators

def bitCount {n : ℕ} (tape : Fin n → Bool) : ℕ :=
  ∑ i, if tape i then 1 else 0

noncomputable def binomialMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  Finset.univ.expect (fun tape : Fin n → Bool => g (bitCount tape))

def splitTape (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Bool × (Fin n → Bool)) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv _ := rfl

theorem bitCount_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    bitCount x = (if x 0 then 1 else 0) + bitCount (fun i => x i.succ) := by
  exact Fin.sum_univ_succ _

theorem mean_congr {n : ℕ} {f g : ℕ → ℝ} (h : ∀ k, f k = g k) :
    binomialMean n f = binomialMean n g := by
  unfold binomialMean
  exact Finset.expect_congr rfl (fun x _ => h (bitCount x))

@[simp] theorem mean_const (n : ℕ) (c : ℝ) :
    binomialMean n (fun _ => c) = c := Fintype.expect_const c

theorem mean_add (n : ℕ) (f g : ℕ → ℝ) :
    binomialMean n (fun k => f k + g k) = binomialMean n f + binomialMean n g :=
  Finset.expect_add_distrib _ _ _

theorem mean_sub (n : ℕ) (f g : ℕ → ℝ) :
    binomialMean n (fun k => f k - g k) = binomialMean n f - binomialMean n g :=
  Finset.expect_sub_distrib _ _ _

theorem mean_mul (n : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    binomialMean n (fun k => c * f k) = c * binomialMean n f := by
  exact (Finset.mul_expect Finset.univ (fun x : Fin n → Bool => f (bitCount x)) c).symm

@[simp] theorem mean_zero (g : ℕ → ℝ) : binomialMean 0 g = g 0 := by
  simp [binomialMean, bitCount]

theorem expect_bool (f : Bool → ℝ) : Finset.univ.expect f = (f false + f true) / 2 := by
  rw [Finset.expect_eq_sum_div_card]
  simp [Fintype.univ_bool, add_comm]

theorem mean_succ (n : ℕ) (g : ℕ → ℝ) :
    binomialMean (n + 1) g =
      (binomialMean n g + binomialMean n (fun k => g (k + 1))) / 2 := by
  unfold binomialMean
  rw [Fintype.expect_equiv (splitTape n)
    (fun x => g (bitCount x))
    (fun x => g ((if x.1 then 1 else 0) + bitCount x.2))
    (fun x => congrArg g (bitCount_succ x))]
  rw [← Finset.univ_product_univ, Finset.expect_product, expect_bool]
  simp [Nat.add_comm]

def score (n k : ℕ) : ℝ := (n : ℝ) - 2 * (k : ℝ)

noncomputable def scoreMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  binomialMean n (fun k => score n k * g k)

@[simp] theorem scoreMean_zero (g : ℕ → ℝ) : scoreMean 0 g = 0 := by
  simp [scoreMean, score]

theorem scoreMean_succ (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g =
      ((scoreMean n g + binomialMean n g) +
       (scoreMean n (fun k => g (k + 1)) -
        binomialMean n (fun k => g (k + 1)))) / 2 := by
  unfold scoreMean
  rw [mean_succ]
  have h₁ : (fun k => score (n + 1) k * g k) =
      (fun k => score n k * g k + g k) := by
    funext k
    simp only [score, Nat.cast_add, Nat.cast_one]
    ring
  have h₂ : (fun k => score (n + 1) (k + 1) * g (k + 1)) =
      (fun k => score n k * g (k + 1) - g (k + 1)) := by
    funext k
    simp only [score, Nat.cast_add, Nat.cast_one]
    ring
  rw [h₁, h₂, mean_add, mean_sub]

/-- Exact finite integration by parts for the fair Boolean-tape law. -/
theorem score_identity (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g = ((n : ℝ) + 1) / 2 *
      (binomialMean n g - binomialMean n (fun k => g (k + 1))) := by
  induction n generalizing g with
  | zero => simp [scoreMean_succ]; ring
  | succ n ih =>
    rw [scoreMean_succ, ih g, ih (fun k => g (k + 1))]
    simp only [mean_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem score_mean_zero (n : ℕ) : binomialMean n (score n) = 0 := by
  cases n with
  | zero => simp [score]
  | succ n =>
    have h := score_identity n (fun _ => 1)
    simpa [scoreMean] using h

/-- The score variance is proved from the actual tape distribution. -/
theorem score_second_moment (n : ℕ) :
    binomialMean n (fun k => score n k ^ 2) = (n : ℝ) := by
  cases n with
  | zero => simp [score]
  | succ n =>
    have h := score_identity n (score (n + 1))
    have hd : binomialMean n (score (n + 1)) -
        binomialMean n (fun k => score (n + 1) (k + 1)) = 2 := by
      rw [← mean_sub]
      calc
        _ = binomialMean n (fun _ => 2) := by
          apply mean_congr
          intro k
          simp only [score, Nat.cast_add, Nat.cast_one]
          ring
        _ = 2 := mean_const _ _
    rw [hd] at h
    simpa [scoreMean, pow_two] using h

theorem score_difference (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g = ((n : ℝ) + 1) *
      (binomialMean n g - binomialMean (n + 1) g) := by
  rw [score_identity, mean_succ]
  ring

/-- Cauchy--Schwarz yields an adjacent-length bound without any support or
small-parameter caveat.  The square form avoids introducing square roots. -/
theorem adjacent_difference_sq (n : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    4 * ((n : ℝ) + 1) *
      (binomialMean n g - binomialMean (n + 1) g) ^ 2 ≤ 1 := by
  have hc : binomialMean (n + 1)
      (fun k => score (n + 1) k * (g k - 1 / 2)) = scoreMean (n + 1) g := by
    calc
      _ = binomialMean (n + 1) (fun k =>
          score (n + 1) k * g k - (1 / 2) * score (n + 1) k) := by
        apply mean_congr
        intro k
        ring
      _ = scoreMean (n + 1) g := by
        rw [mean_sub, mean_mul, score_mean_zero]
        simp [scoreMean]
  have hv : binomialMean (n + 1) (fun k => (g k - 1 / 2) ^ 2) ≤ 1 / 4 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro tape _
    have h₀ := (hg (bitCount tape)).1
    have h₁ := (hg (bitCount tape)).2
    have hp := mul_nonneg h₀ (sub_nonneg.mpr h₁)
    nlinarith
  have hcs : (binomialMean (n + 1)
        (fun k => score (n + 1) k * (g k - 1 / 2))) ^ 2 ≤
      binomialMean (n + 1) (fun k => score (n + 1) k ^ 2) *
        binomialMean (n + 1) (fun k => (g k - 1 / 2) ^ 2) :=
    Finset.expect_mul_sq_le_sq_mul_sq Finset.univ _ _
  rw [hc, score_difference, score_second_moment] at hcs
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hv (le_of_lt hn)
  simp only [Nat.cast_add, Nat.cast_one] at hcs
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith

theorem adjacent_difference_le (n : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrn : r ^ 2 ≤ 4 * ((n : ℝ) + 1)) :
    |binomialMean n g - binomialMean (n + 1) g| ≤ 1 / r := by
  have hs := adjacent_difference_sq n g hg
  have hd := sq_nonneg (binomialMean n g - binomialMean (n + 1) g)
  have hh := mul_le_mul_of_nonneg_right hrn hd
  rw [le_div_iff₀ hr]
  have ha := sq_abs (binomialMean n g - binomialMean (n + 1) g)
  have hp : 0 ≤ |binomialMean n g - binomialMean (n + 1) g| * r :=
    mul_nonneg (abs_nonneg _) (le_of_lt hr)
  nlinarith [sq_nonneg (|binomialMean n g - binomialMean (n + 1) g| * r - 1)]

theorem mean_shift_le (n d : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrn : r ^ 2 ≤ 4 * ((n : ℝ) + 1)) :
    |binomialMean (n + d) g - binomialMean n g| ≤ (d : ℝ) / r := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hrnd : r ^ 2 ≤ 4 * ((n + d : ℕ) + 1 : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      linarith
    have ha := adjacent_difference_le (n + d) g hg r hr hrnd
    rw [abs_sub_comm] at ha
    calc
      _ ≤ |binomialMean (n + d + 1) g - binomialMean (n + d) g| +
          |binomialMean (n + d) g - binomialMean n g| := abs_sub_le _ _ _
      _ ≤ 1 / r + (d : ℝ) / r := add_le_add ha ih
      _ = ((d + 1 : ℕ) : ℝ) / r := by push_cast; ring

theorem mean_ordered_difference_le (m n : ℕ) (hmn : m ≤ n) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrm : r ^ 2 ≤ 4 * ((m : ℝ) + 1)) :
    |binomialMean n g - binomialMean m g| ≤ ((n - m : ℕ) : ℝ) / r := by
  simpa [Nat.add_sub_of_le hmn] using mean_shift_le m (n - m) g hg r hr hrm

theorem mean_window_le (N M m : ℕ) (hlo : N - M ≤ m) (hhi : m ≤ N + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (r : ℝ) (hr : 0 < r) (hbase : r ^ 2 ≤ 4 * (((N - M : ℕ) : ℝ) + 1)) :
    |binomialMean m g - binomialMean N g| ≤ (M : ℝ) / r := by
  by_cases hmN : m ≤ N
  · have hrm : r ^ 2 ≤ 4 * ((m : ℝ) + 1) := by
      have : ((N - M : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlo
      linarith
    have h := mean_ordered_difference_le m N hmN g hg r hr hrm
    rw [abs_sub_comm] at h
    refine h.trans (div_le_div_of_nonneg_right ?_ (le_of_lt hr))
    have : N - m ≤ M := by omega
    exact_mod_cast this
  · have hNm : N ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmN)
    have hrN : r ^ 2 ≤ 4 * ((N : ℝ) + 1) := by
      have : ((N - M : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N M
      linarith
    have h := mean_ordered_difference_le N m hNm g hg r hr hrN
    refine h.trans (div_le_div_of_nonneg_right ?_ (le_of_lt hr))
    have : m - N ≤ M := by omega
    exact_mod_cast this

/-- A convenient square center for a fixed alphabet. -/
theorem square_window_le (q M m : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    |binomialMean m g - binomialMean ((4 * q * M) ^ 2) g| ≤ 1 / (4 * (q : ℝ)) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hR : (4 : ℝ) * M ≤ ((4 * q * M : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hRM : (M : ℝ) ≤ (((4 * q * M : ℕ) : ℝ)) ^ 2 := by nlinarith
  have hMN : M ≤ (4 * q * M) ^ 2 := by exact_mod_cast hRM
  have hr : (0 : ℝ) < ((4 * q * M : ℕ) : ℝ) := by linarith
  have hb : (((4 * q * M : ℕ) : ℝ)) ^ 2 ≤
      4 * (((((4 * q * M) ^ 2 - M : ℕ)) : ℝ) + 1) := by
    rw [Nat.cast_sub hMN, Nat.cast_pow]
    nlinarith
  have h := mean_window_le ((4 * q * M) ^ 2) M m hlo hhi g hg
    ((4 * q * M : ℕ) : ℝ) hr hb
  have he : (M : ℝ) / ((4 * q * M : ℕ) : ℝ) = 1 / (4 * (q : ℝ)) := by
    push_cast
    have hq0 : (q : ℝ) ≠ 0 := by linarith
    have hM0 : (M : ℝ) ≠ 0 := by linarith
    field_simp
  rw [he] at h
  exact h

/-- A modal event of probability at least `1/q` retains probability `1/(2q)`
throughout the middle window used in lazy-walk powering. -/
theorem modal_transfer (q M m : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (hmodal : 1 / (q : ℝ) ≤ binomialMean ((4 * q * M) ^ 2) g) :
    1 / (2 * (q : ℝ)) ≤ binomialMean m g := by
  have h := square_window_le q M m hq hM hlo hhi g hg
  have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hrec : 0 < 1 / (q : ℝ) := one_div_pos.mpr hqR
  have he₁ : 1 / (4 * (q : ℝ)) = (1 / (q : ℝ)) / 4 := by ring
  have he₂ : 1 / (2 * (q : ℝ)) = (1 / (q : ℝ)) / 2 := by ring
  rw [he₁] at h
  rw [he₂]
  have hl := (abs_le.mp h).1
  linarith

end UniqueGamesTheorem.Foundations.PCP.LazySmoothing

end

end OAI
