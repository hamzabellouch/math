import Mathlib
import OAI.Computability.MinUncut.Machines.RuntimeModel
import OAI.Computability.MinUncut.PCP.ContextClear
import OAI.Computability.MinUncut.Machines.MachineTupleOdometer

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceOccurrences.Encoding

open MinUncutGames.Foundations.Complexity.MachineTupleOdometer

def decodeTuple {α β : Type} (a : Encoding α) (b : Encoding β)
    (digits : Fin a.size → Fin b.size) : α → β :=
  fun x => b.code.symm (digits (a.code x))

theorem enumerate_function {α β : Type} (a : Encoding α) (b : Encoding β) :
    (a.function b).enumerate =
      (tupleOrder b.size a.size).map (decodeTuple a b) := by
  simp only [tupleOrder, List.map_ofFn]
  rfl

theorem enumerate_fin_function (n u : ℕ) :
    ((Encoding.fin u).function (Encoding.fin n)).enumerate = tupleOrder n u := by
  rfl

end MinUncutGames.Foundations.Hastad.SourceOccurrences.Encoding

namespace MinUncutGames.Foundations.Hastad.SourceLoopOrder

open Complexity Complexity.MachineTupleOdometer
open Target SourceContexts SourceOccurrences
open MinUncutGames.Reduction

def tupleTapeOrder (u D : ℕ) : List (SourceTape.TestTape (I u) (J u) D) :=
  (tupleOrder 2 (2 ^ u)).flatMap (fun f =>
    (tupleOrder D (8 ^ u)).flatMap (fun z =>
      (tupleOrder 2 (8 ^ u)).map (fun g =>
        (Encoding.decodeTuple (iEncoding u) Encoding.bool f,
         Encoding.decodeTuple (jEncoding u) (Encoding.fin D) z,
         Encoding.decodeTuple (jEncoding u) Encoding.bool g))))

theorem testTapeEncoding_eq_tupleTapeOrder (u D : ℕ) :
    (testTapeEncoding u D).enumerate = tupleTapeOrder u D := by
  rw [SourceEnumeration.testTapeEncoding_enumerate]
  simp only [tupleTapeOrder, Encoding.enumerate_function,
    List.flatMap_map, List.map_map, Function.comp_def]
  rfl

theorem testTapeEncoding_flatMap_tupleTapeOrder {α : Type} (u D : ℕ)
    (emit : SourceTape.TestTape (I u) (J u) D → List α) :
    (testTapeEncoding u D).enumerate.flatMap emit =
      (tupleTapeOrder u D).flatMap emit := by
  rw [testTapeEncoding_eq_tupleTapeOrder]

def rankedQuery (u D : ℕ) (fallback : SourceQueryLoop.Query u D)
    (i : ℕ) : SourceQueryLoop.Query u D :=
  if h : i < (testTapeEncoding u D).size then
    (testTapeEncoding u D).code.symm ⟨i, h⟩
  else fallback

theorem rankedQuery_at (u D : ℕ) (fallback : SourceQueryLoop.Query u D)
    (i : Fin (testTapeEncoding u D).size) :
    rankedQuery u D fallback i.val = (testTapeEncoding u D).code.symm i := by
  simp only [rankedQuery, i.isLt, ↓reduceDIte]

theorem query_prefixBits_eq_ofFn (u D n : ℕ) (queries : ℕ → SourceQueryLoop.Query u D)
    (values : Fin 3 → ℕ) (signature : SourceLocalSignature.Signature u) :
    SourceQueryLoop.prefixBits u D queries values signature n =
      (List.ofFn (fun i : Fin n => queries i.val)).flatMap
        (fun query => SourceTestAppend.equationBits u D values (signature, query)) := by
  induction n with
  | zero => simp [SourceQueryLoop.prefixBits]
  | succ n ih =>
    rw [SourceQueryLoop.prefixBits, List.ofFn_succ', List.concat_eq_append,
      List.flatMap_append]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Fin.val_castSucc, Fin.val_last] using
      congrArg (fun bits => bits ++
        SourceTestAppend.equationBits u D values (signature, queries n)) ih

theorem query_prefixBits_eq_enumerate (u D : ℕ) (fallback : SourceQueryLoop.Query u D)
    (values : Fin 3 → ℕ) (signature : SourceLocalSignature.Signature u) :
    SourceQueryLoop.prefixBits u D (rankedQuery u D fallback) values signature
        (testTapeEncoding u D).size =
      (testTapeEncoding u D).enumerate.flatMap
        (fun query => SourceTestAppend.equationBits u D values (signature, query)) := by
  rw [query_prefixBits_eq_ofFn]
  have hlist : List.ofFn (fun i : Fin (testTapeEncoding u D).size =>
      rankedQuery u D fallback i.val) = (testTapeEncoding u D).enumerate := by
    apply congrArg List.ofFn
    funext i
    exact rankedQuery_at u D fallback i
  rw [hlist]

theorem query_prefixBits_eq_tupleTapeOrder (u D : ℕ)
    (fallback : SourceQueryLoop.Query u D) (values : Fin 3 → ℕ)
    (signature : SourceLocalSignature.Signature u) :
    SourceQueryLoop.prefixBits u D (rankedQuery u D fallback) values signature
        (testTapeEncoding u D).size =
      (tupleTapeOrder u D).flatMap
        (fun query => SourceTestAppend.equationBits u D values (signature, query)) := by
  rw [query_prefixBits_eq_enumerate, testTapeEncoding_eq_tupleTapeOrder]

def tupleSourceOrder (F : Formula) (u D : ℕ) : List (SourceIndex F u D) :=
  (tupleOrder F.clauses.length u).flatMap (fun c =>
    (tupleOrder 3 u).flatMap (fun s =>
      (tupleTapeOrder u D).map (fun t =>
        ((c, Encoding.decodeTuple (Encoding.fin u) slotEncoding s), t))))

theorem sourceIndexEncoding_eq_tupleSourceOrder (F : Formula) (u D : ℕ) :
    (sourceIndexEncoding F u D).enumerate = tupleSourceOrder F u D := by
  rw [SourceEnumeration.sourceIndexEncoding_enumerate]
  simp only [tupleSourceOrder, tupleTapeOrder, clauseEncoding, slotContextEncoding,
    Encoding.enumerate_function, List.flatMap_map, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro c hc
  apply List.flatMap_congr
  intro slots hslots
  erw [List.map_flatMap]
  apply List.flatMap_congr
  intro first hfirst
  erw [List.map_flatMap]
  apply List.flatMap_congr
  intro second hsecond
  erw [List.map_map]
  rfl

theorem rawSourceList_eq_tupleOrder (F : Formula) (u D : ℕ) :
    rawSourceList F u D = (tupleSourceOrder F u D).map (sourceEquation F u D) := by
  unfold rawSourceList occurrenceList
  rw [sourceIndexEncoding_eq_tupleSourceOrder]

theorem sourceList_eq_tupleOrder (F : Formula) (u D : ℕ) (hne : F.clauses ≠ []) :
    sourceList F u D = (tupleSourceOrder F u D).map (sourceEquation F u D) := by
  rw [sourceList_nonempty F u D hne, rawSourceList_eq_tupleOrder]

theorem rawSourceList_flatMap_tupleOrder {α : Type} (F : Formula) (u D : ℕ)
    (emit : CloneGap.Equation (Fin (nBits F u)) → List α) :
    (rawSourceList F u D).flatMap emit =
      (tupleSourceOrder F u D).flatMap (fun p => emit (sourceEquation F u D p)) := by
  rw [rawSourceList_eq_tupleOrder]
  simp only [List.flatMap_map]

def reverseAppend {α β : Type} (encode : α → List β)
    (accumulator : List β) (record : α) : List β :=
  (encode record).reverse ++ accumulator

theorem foldl_reverseAppend {α β : Type} (encode : α → List β)
    (records : List α) (accumulator : List β) :
    records.foldl (reverseAppend encode) accumulator =
      (records.flatMap encode).reverse ++ accumulator := by
  induction records generalizing accumulator with
  | nil => simp
  | cons record records ih =>
    simp only [List.foldl_cons, ih, reverseAppend, List.flatMap_cons,
      List.reverse_append, List.append_assoc]

theorem foldl_reverseAppend_header {α β : Type} (encode : α → List β)
    (records : List α) (header : List β) :
    records.foldl (reverseAppend encode) header.reverse =
      (header ++ records.flatMap encode).reverse := by
  rw [foldl_reverseAppend, List.reverse_append]

theorem foldl_reverseAppend_prefix {α β : Type} (encode : α → List β)
    (emitted remaining : List α) (header : List β) :
    (emitted ++ remaining).foldl (reverseAppend encode) header.reverse =
      remaining.foldl (reverseAppend encode)
        (header ++ emitted.flatMap encode).reverse := by
  rw [List.foldl_append, foldl_reverseAppend_header]

theorem foldl_resultTapes {α K : Type} [DecidableEq K]
    (layout : SourceTestAppend.Layout K) (encode : α → List Bool)
    (records : List α) (base : K → List Bool) :
    records.foldl (fun tapes record =>
        SourceTestAppend.resultTapes layout tapes (encode record)) base =
      Function.update base layout.accumulator
        ((records.flatMap encode).reverse ++ base layout.accumulator) := by
  induction records generalizing base with
  | nil =>
    funext k
    by_cases hk : k = layout.accumulator <;> simp [hk]
  | cons record records ih =>
    simp only [List.foldl_cons, ih]
    funext k
    by_cases hk : k = layout.accumulator <;>
      simp [SourceTestAppend.resultTapes, hk, List.flatMap_cons,
        List.reverse_append, List.append_assoc]

theorem inputBits_eq_header_records (input : SourceEncoding.Input) :
    SourceEncoding.inputBits input =
      encodeWords [input.«variables», input.equations.length] ++
        input.equations.flatMap (fun e => encodeWords (SourceEncoding.equationWords e)) := by
  unfold SourceEncoding.inputBits SourceEncoding.inputWords
  rw [encodeWords_append]
  congr 1
  induction input.equations with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons, encodeWords_append, ih]

theorem input_reverse_accumulator (input : SourceEncoding.Input) :
    input.equations.foldl
        (reverseAppend (fun e => encodeWords (SourceEncoding.equationWords e)))
        (encodeWords [input.«variables», input.equations.length]).reverse =
      (SourceEncoding.inputBits input).reverse := by
  rw [foldl_reverseAppend_header, inputBits_eq_header_records]

theorem sourceInput_tuple_reverse_accumulator (F : Formula) (u D : ℕ)
    (hD : 0 < D) (hne : F.clauses ≠ []) :
    (tupleSourceOrder F u D).foldl
        (reverseAppend (fun p => encodeWords
          (SourceEncoding.equationWords (sourceEquation F u D p))))
        (encodeWords [nBits F u, (sourceList F u D).length]).reverse =
      (SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
  rw [← input_reverse_accumulator (sourceInput F u D hD)]
  change _ = (sourceList F u D).foldl
    (reverseAppend (fun e => encodeWords (SourceEncoding.equationWords e)))
    (encodeWords [nBits F u, (sourceList F u D).length]).reverse
  rw [sourceList_eq_tupleOrder F u D hne, List.foldl_map]
  rfl

theorem finalReverse_steps (input : SourceEncoding.Input) (register : Option Bool) :
    MachineReverse.next^[(SourceEncoding.inputBits input).length + 1]
      (some (MachineReverse.running
        (input.equations.foldl
          (reverseAppend (fun e => encodeWords (SourceEncoding.equationWords e)))
          (encodeWords [input.«variables», input.equations.length]).reverse)
        [] register)) =
      some (MachineReverse.halted (SourceEncoding.inputBits input)) := by
  rw [input_reverse_accumulator]
  simpa only [List.length_reverse, List.reverse_reverse, List.append_nil] using
    MachineReverse.reverse_steps (SourceEncoding.inputBits input).reverse [] register

end MinUncutGames.Foundations.Hastad.SourceLoopOrder

end
section
namespace MinUncutGames.Foundations.Hastad.SourceQueryOrder

open Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceAddressDescriptors SourceLoopOrder

def occurrenceBits (F : Formula) (u D : Nat) (p : SourceIndex F u D) : List Bool :=
  encodeWords (MinUncutGames.Reduction.SourceEncoding.equationWords (sourceEquation F u D p))

def slotBits (F : Formula) (u D : Nat) (c : ClauseContext F u) (s : SlotContext u) :
    List Bool :=
  (testTapeEncoding u D).enumerate.flatMap (fun t => occurrenceBits F u D ((c, s), t))

def tupleBits (F : Formula) (u D : Nat) (c : ClauseContext F u) : List Bool :=
  (slotContextEncoding u).enumerate.flatMap (slotBits F u D c)

theorem equationBits_eq (F : Formula) (u D : Nat) (c : ClauseContext F u)
    (s : SlotContext u) (t : SourceQueryLoop.Query u D) :
    SourceTestAppend.equationBits u D (baseValue F u c (sampledVariables F c s))
      (ofContext F c s, t) = occurrenceBits F u D ((c, s), t) := by
  rw [occurrenceBits, sourceEquation_words]
  rfl

theorem prefixBits_eq_slotBits (F : Formula) (u D : Nat) (c : ClauseContext F u)
    (s : SlotContext u) (fallback : SourceQueryLoop.Query u D) :
    SourceQueryLoop.prefixBits u D (rankedQuery u D fallback)
      (baseValue F u c (sampledVariables F c s)) (ofContext F c s)
      (testTapeEncoding u D).size = slotBits F u D c s := by
  rw [query_prefixBits_eq_enumerate]
  unfold slotBits
  congr 1
  funext t
  exact equationBits_eq F u D c s t

variable {K Λ : Type} [DecidableEq K]

theorem sourceLoopInTime (F : Formula) (u D : Nat) (c : ClauseContext F u)
    (s : SlotContext u) (fallback initialQuery : SourceQueryLoop.Query u D)
    (layout : SourceTestAppend.Layout K)
    (labels : SourceQueryLoop.Label u D (testTapeEncoding u D).size → Λ)
    (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (SourceQueryLoop.State u D))
    (atLabels : ∀ l, p (labels l) = SourceQueryLoop.statement u D
      (testTapeEncoding u D).size (rankedQuery u D fallback) layout labels exit l)
    (base : K → List Bool)
    (sourceWords : ∀ side, base (layout.sources side) =
      encodeWord (baseValue F u c (sampledVariables F c s) side))
    (scratchEmpty : base layout.scratch = [])
    (temporaryEmpty : base layout.temporary = []) :
    ∃ lastQuery : SourceQueryLoop.Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step p)
        ⟨some (labels (.load ⟨0, Nat.zero_lt_succ _⟩)),
          ((ofContext F c s, initialQuery), none), base⟩
        (some ⟨exit, ((ofContext F c s, lastQuery), none),
          SourceTestAppend.resultTapes layout base (slotBits F u D c s)⟩)
        ((testTapeEncoding u D).size * (9 * nBits F u + 21) + 1)) := by
  have hbound : ∀ i, i < (testTapeEncoding u D).size →
      SourceTestAppend.steps u D (baseValue F u c (sampledVariables F c s))
        (ofContext F c s, rankedQuery u D fallback i) ≤ 9 * nBits F u + 20 := by
    intro i hi
    let run := SourceTestAppend.sourceAppendInTime F u D
      ((c, s), rankedQuery u D fallback i) layout
      (fun l => labels (.emit ⟨i, hi⟩ l))
      (some (labels (.load ⟨i + 1, by omega⟩))) p
      (fun l => atLabels (.emit ⟨i, hi⟩ l)) base sourceWords
      scratchEmpty temporaryEmpty none
    exact run.steps_le_m
  have h := SourceQueryLoop.loopInTime u D (testTapeEncoding u D).size
    (9 * nBits F u + 20) (rankedQuery u D fallback) layout labels exit p atLabels
    (ofContext F c s) initialQuery base (baseValue F u c (sampledVariables F c s))
    sourceWords scratchEmpty temporaryEmpty hbound
  rw [prefixBits_eq_slotBits] at h
  exact h

end MinUncutGames.Foundations.Hastad.SourceQueryOrder

end
section
namespace MinUncutGames.Foundations.Hastad.SourceTupleTape

open Turing Complexity SourceContexts SourceRuntimeModel

structure Snapshot where
  rank : List Bool := []
  rightBase : List Bool := []
  leftBase : List Bool := []
  zero : List Bool := []
  emitted : List Bool := []
  deriving DecidableEq, Inhabited

variable {u : Nat} {Extra : Type}

def tapes (base : Arena u Extra → List Bool) (s : Snapshot) : Arena u Extra → List Bool
  | .extra (.inr .rank) => s.rank
  | .extra (.inr .rightBase) => s.rightBase
  | .extra (.inr .leftBase) => s.leftBase
  | .extra (.inr .zero) => s.zero
  | .extra (.inr .accumulator) => s.emitted.reverse ++ base (workTape .accumulator)
  | k => base k

@[simp] theorem tapes_rank (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .rank) = s.rank := rfl
@[simp] theorem tapes_rightBase (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .rightBase) = s.rightBase := rfl
@[simp] theorem tapes_leftBase (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .leftBase) = s.leftBase := rfl
@[simp] theorem tapes_zero (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .zero) = s.zero := rfl
@[simp] theorem tapes_accumulator (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .accumulator) = s.emitted.reverse ++ base (workTape .accumulator) := rfl
@[simp] theorem tapes_coefficient (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .coefficient) = base (workTape .coefficient) := rfl
@[simp] theorem tapes_dummy (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .dummy) = base (workTape .dummy) := rfl
@[simp] theorem tapes_leftBlock (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .leftBlock) = base (workTape .leftBlock) := rfl
@[simp] theorem tapes_queryTemporary (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .queryTemporary) = base (workTape .queryTemporary) := rfl
@[simp] theorem tapes_queryScratch (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .queryScratch) = base (workTape .queryScratch) := rfl
@[simp] theorem tapes_field (base : Arena u Extra → List Bool) (s : Snapshot) (j : Fin u) (k : Fin 6) :
    tapes base s (.field j k) = base (.field j k) := rfl
@[simp] theorem tapes_current (base : Arena u Extra → List Bool) (s : Snapshot) (j : Fin u) :
    tapes base s (.current j) = base (.current j) := rfl
@[simp] theorem tapes_formula (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .formula = base .formula := rfl
@[simp] theorem tapes_index (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .index = base .index := rfl
@[simp] theorem tapes_work (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .work = base .work := rfl
@[simp] theorem tapes_variableHeader (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s variableHeader = base variableHeader := rfl
@[simp] theorem tapes_clauseHeader (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s clauseHeader = base clauseHeader := rfl

variable [DecidableEq Extra]

theorem update_rank (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .rank) value = tapes base {s with rank := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_rightBase (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .rightBase) value = tapes base {s with rightBase := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_leftBase (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .leftBase) value = tapes base {s with leftBase := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_zero (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .zero) value = tapes base {s with zero := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_emitted (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .accumulator)
      (value.reverse ++ base (workTape .accumulator)) = tapes base {s with emitted := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem query_result (base : Arena u Extra → List Bool) (s : Snapshot) (bits : List Bool) :
    SourceTestAppend.resultTapes queryLayout (tapes base s) bits =
      tapes base {s with emitted := s.emitted ++ bits} := by
  change Function.update (tapes base s) (workTape .accumulator)
    (bits.reverse ++ tapes base s (workTape .accumulator)) = _
  rw [tapes_accumulator]
  have h := update_emitted base s (s.emitted ++ bits)
  simpa only [List.reverse_append, List.append_assoc] using h

theorem horner_clause_result (base : Arena u Extra → List Bool) (s : Snapshot) (value : Nat) :
    MachineHorner.resultTapes clauseRankSlots (tapes base s) value =
      tapes base {s with rank := encodeWord value ++ s.rank} := by
  change Function.update (tapes base s) (workTape .rank)
    (encodeWord value ++ tapes base s (workTape .rank)) = _
  rw [tapes_rank, update_rank]

theorem horner_variable_result (base : Arena u Extra → List Bool) (s : Snapshot)
    (selected : SlotContext u) (value : Nat) :
    MachineHorner.resultTapes (variableRankSlots selected) (tapes base s) value =
      tapes base {s with rank := encodeWord value ++ s.rank} := by
  change Function.update (tapes base s) (workTape .rank)
    (encodeWord value ++ tapes base s (workTape .rank)) = _
  rw [tapes_rank, update_rank]

theorem horner_right_result (base : Arena u Extra → List Bool) (s : Snapshot) (value : Nat) :
    MachineHorner.resultTapes (baseSlots true) (tapes base s) value =
      tapes base {s with rightBase := encodeWord value ++ s.rightBase} := by
  change Function.update (tapes base s) (workTape .rightBase)
    (encodeWord value ++ tapes base s (workTape .rightBase)) = _
  rw [tapes_rightBase, update_rightBase]

theorem horner_left_result (base : Arena u Extra → List Bool) (s : Snapshot) (value : Nat) :
    MachineHorner.resultTapes (baseSlots false) (tapes base s) value =
      tapes base {s with leftBase := encodeWord value ++ s.leftBase} := by
  change Function.update (tapes base s) (workTape .leftBase)
    (encodeWord value ++ tapes base s (workTape .leftBase)) = _
  rw [tapes_leftBase, update_leftBase]

structure WorkClean (base : Arena u Extra → List Bool) : Prop where
  accA : base (workTape .accA) = []
  accB : base (workTape .accB) = []
  counter : base (workTape .counter) = []
  scratch : base (workTape .arithScratch) = []

omit [DecidableEq Extra] in
theorem clean_clause (base : Arena u Extra → List Bool) (s : Snapshot) (clean : WorkClean base) :
    MachineHorner.Clean clauseRankSlots (tapes base s) where
  accA := clean.accA
  accB := clean.accB
  counter := clean.counter
  scratch := clean.scratch

omit [DecidableEq Extra] in
theorem clean_variable (base : Arena u Extra → List Bool) (s : Snapshot) (selected : SlotContext u)
    (clean : WorkClean base) : MachineHorner.Clean (variableRankSlots selected) (tapes base s) where
  accA := clean.accA
  accB := clean.accB
  counter := clean.counter
  scratch := clean.scratch

omit [DecidableEq Extra] in
theorem clean_base (base : Arena u Extra → List Bool) (s : Snapshot) (right : Bool)
    (clean : WorkClean base) : MachineHorner.Clean (baseSlots right) (tapes base s) where
  accA := clean.accA
  accB := clean.accB
  counter := clean.counter
  scratch := clean.scratch

omit [DecidableEq Extra] in
theorem tapes_coordinateOutput {numVariables : ℕ} (j : Fin u) (clause : Target.Clause numVariables)
    (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes (SourceContextLoad.coordinateOutput j clause base) s =
      SourceContextLoad.coordinateOutput j clause (tapes base s) := by
  funext k
  cases k <;> simp [tapes, SourceContextLoad.coordinateOutput, workTape]
  rename_i extra
  cases extra with
  | inl header => rfl
  | inr role => cases role <;> rfl

omit [DecidableEq Extra] in

theorem tapes_stageTapes (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (s : Snapshot) (r : Nat) :
    tapes (SourceContextLoad.stageTapes F c base r) s =
      SourceContextLoad.stageTapes F c (tapes base s) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [SourceContextLoad.stageTapes]
    split
    · rw [tapes_coordinateOutput, ih]
    · exact ih

theorem final_tapes (base : Arena u Extra → List Bool) (emitted : List Bool)
    (hrank : base (workTape .rank) = []) (hright : base (workTape .rightBase) = [])
    (hleft : base (workTape .leftBase) = []) (hzero : base (workTape .zero) = []) :
    tapes base {emitted := emitted} =
      Function.update base (workTape .accumulator) (emitted.reverse ++ base (workTape .accumulator)) := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role =>
    cases role <;> simp_all [tapes, workTape]

theorem empty_tapes (base : Arena u Extra → List Bool)
    (hrank : base (workTape .rank) = []) (hright : base (workTape .rightBase) = [])
    (hleft : base (workTape .leftBase) = []) (hzero : base (workTape .zero) = []) :
    tapes base {} = base := by
  simpa using final_tapes base [] hrank hright hleft hzero

omit [DecidableEq Extra] in
theorem clear_loaded (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (s : Snapshot)
    (hfields : ∀ j k, base (.field j k) = []) (hindex : base .index = []) (hwork : base .work = []) :
    SourceContextClear.outputTapes (tapes (SourceContextLoad.stageTapes F c base u) s) = tapes base s := by
  rw [tapes_stageTapes]
  exact SourceContextClear.output_loaded_eq_base F c (tapes base s) hfields hindex hwork

def clearLoadedSnapshotInTime (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (s : Snapshot)
    (hfields : ∀ j k, base (.field j k) = []) (hindex : base .index = []) (hwork : base .work = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step SourceContextClear.program)
      ⟨some SourceContextClear.main, ((), register), tapes (SourceContextLoad.stageTapes F c base u) s⟩
      (some ⟨none, ((), none), tapes base s⟩)
      (6 * u * ((formulaBits F).length + 1) + 1) := by
  rw [tapes_stageTapes]
  exact SourceContextClear.clearLoadedToBaseInTime F c (tapes base s) hfields hindex hwork register

end MinUncutGames.Foundations.Hastad.SourceTupleTape

end

end OAI
