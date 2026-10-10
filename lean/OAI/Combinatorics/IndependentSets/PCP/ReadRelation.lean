import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.RawInitialMachineBudget
import OAI.Combinatorics.IndependentSets.Machines.MachineComposition

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.ReadRelation

open Turing
open IndependentSetsGames.Foundations.Complexity
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

end IndependentSetsGames.Foundations.PCP.AlphabetTable.ReadRelation

end OAI
