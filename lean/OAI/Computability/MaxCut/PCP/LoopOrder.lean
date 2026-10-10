import Mathlib
import OAI.Computability.MaxCut.PCP.DescriptorEmission
import OAI.Computability.MaxCut.Machines.MachineTupleOdometer

namespace OAI

section

namespace MaxCutGames.Foundations.Hastad.SourceOccurrences.Encoding

open MaxCutGames.Foundations.Complexity.MachineTupleOdometer

/-- Interpret a radix tuple using the declared domain and codomain numbering. -/
def decodeTuple {α β : Type} (a : Encoding α) (b : Encoding β)
    (digits : Fin a.size → Fin b.size) : α → β :=
  fun x => b.code.symm (digits (a.code x))

/-- Increasing function rank is exactly the controller's tuple order, followed
by the explicit coordinate decoder. This includes empty domains and codomains. -/
theorem enumerate_function {α β : Type} (a : Encoding α) (b : Encoding β) :
    (a.function b).enumerate =
      (tupleOrder b.size a.size).map (decodeTuple a b) := by
  simp only [tupleOrder, List.map_ofFn]
  rfl

theorem enumerate_fin_function (n u : ℕ) :
    ((Encoding.fin u).function (Encoding.fin n)).enumerate = tupleOrder n u := by
  rfl

end MaxCutGames.Foundations.Hastad.SourceOccurrences.Encoding

namespace MaxCutGames.Foundations.Hastad.SourceLoopOrder

open Complexity Complexity.MachineTupleOdometer
open Target SourceContexts SourceOccurrences
open MaxCutGames.Reduction

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

/-- Total extension of the declared tape decoder, for the query loop's natural
index register. Out-of-range values are never visited by that loop. -/
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

/-- Clause, slot, left-query, noise, right-query loops, from outermost to
innermost. Within each tuple loop coordinate zero changes fastest. -/
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

/-- Equality of ordered equation lists preserves every repeated occurrence. -/
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

/-- The stack update performed by one record append. -/
def reverseAppend {α β : Type} (encode : α → List β)
    (accumulator : List β) (record : α) : List β :=
  (encode record).reverse ++ accumulator

/-- After any ascending prefix, the accumulator is its reversed encoding
followed by the original accumulator. -/
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

/-- The prefix invariant is stated without requiring that the prefix end on
the last record. A later suffix continues from exactly this accumulator. -/
theorem foldl_reverseAppend_prefix {α β : Type} (encode : α → List β)
    (emitted remaining : List α) (header : List β) :
    (emitted ++ remaining).foldl (reverseAppend encode) header.reverse =
      remaining.foldl (reverseAppend encode)
        (header ++ emitted.flatMap encode).reverse := by
  rw [List.foldl_append, foldl_reverseAppend_header]

/-- The actual tape update used by `SourceTestAppend` has this same invariant;
all other tapes remain the original tapes. -/
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

/-- The nonempty-formula branch can feed the accumulator directly from the
tuple controller's occurrence order. The total-input invariant above also
covers the separate singleton empty-formula branch. -/
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

/-- Applying the existing reversal machine to the accumulated records returns
the exact serialized input in `inputBits.length + 1` transitions. This is only
the final reversal stage, not a bound for generating the records. -/
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

end MaxCutGames.Foundations.Hastad.SourceLoopOrder

end

namespace MaxCutGames.Foundations.Hastad.SourceOdometerSchedule

open Turing Complexity MachineTupleOdometer
open Reduction.MachineTransfer

abbrev Tape := SourceContextLoad.Tape

variable {u m : ℕ} {Extra Λ σ : Type} [DecidableEq Extra]

def currentAt (accumulator : Extra) (i : ℕ) : Tape u Extra :=
  if h : i < u then .current ⟨i, h⟩ else .extra accumulator

def remainingAt (accumulator : Extra) (i : ℕ) : Tape u Extra :=
  if h : i < u then .remaining ⟨i, h⟩ else .extra accumulator

/-- Set the active low coordinates; higher digits and every other tape retain
their original contents. Unary digit stacks have no unread suffix. -/
def setDigits (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) : Tape u Extra → List Bool
  | .current i => if h : i.val < q then encodeWord (digits ⟨i.val, h⟩)
      else base (.current i)
  | .remaining i => if h : i.val < q then encodeWord (m - 1 - digits ⟨i.val, h⟩)
      else base (.remaining i)
  | k => base k

def setAcc (accumulator : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    Tape u Extra → List Bool := Function.update base (.extra accumulator) bits

def putDigit (i : Fin u) (base : Tape u Extra → List Bool) (d r : ℕ) :
    Tape u Extra → List Bool := digitTapes (.current i) (.remaining i) base d r [] []

omit [DecidableEq Extra] in
@[simp] theorem setDigits_zero (m : ℕ) (digits : Fin 0 → ℕ)
    (base : Tape u Extra → List Bool) : setDigits m digits base = base := by
  funext k
  cases k <;> simp [setDigits]

omit [DecidableEq Extra] in
@[simp] theorem setDigits_extra (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) (a : Extra) :
    setDigits m digits base (.extra a) = base (.extra a) := rfl

@[simp] theorem setAcc_self (a : Extra) (base : Tape u Extra → List Bool) :
    setAcc a base (base (.extra a)) = base := by
  simp [setAcc]

@[simp] theorem setAcc_setAcc (a : Extra) (base : Tape u Extra → List Bool)
    (first second : List Bool) : setAcc a (setAcc a base first) second = setAcc a base second := by
  simp [setAcc]

@[simp] theorem setAcc_apply (a : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    setAcc a base bits (.extra a) = bits := by simp [setAcc]

theorem setDigits_setAcc (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (a : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    setDigits m digits (setAcc a base bits) = setAcc a (setDigits m digits base) bits := by
  funext k
  cases k <;> simp [setDigits, setAcc, Function.update_apply]

@[simp] theorem putDigit_extra (i : Fin u) (base : Tape u Extra → List Bool)
    (d r : ℕ) (a : Extra) : putDigit i base d r (.extra a) = base (.extra a) := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

theorem putDigit_setAcc (i : Fin u) (base : Tape u Extra → List Bool)
    (d r : ℕ) (a : Extra) (bits : List Bool) :
    putDigit i (setAcc a base bits) d r = setAcc a (putDigit i base d r) bits := by
  funext k
  cases k <;> simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
    setAcc, Function.update_apply]

/-- The low-coordinate assignment commutes with a separate higher digit. -/
theorem setDigits_putDigit (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) (d r : ℕ) :
    setDigits m digits (putDigit ⟨q, hq⟩ base d r) =
      putDigit ⟨q, hq⟩ (setDigits m digits base) d r := by
  funext k
  cases k with
  | current i =>
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi, hne]
    · simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi,
        Function.update_apply]
  | remaining i =>
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi, hne]
    · simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi,
        Function.update_apply]
  | _ => simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

/-- The last coordinate is the outside loop coordinate. -/
theorem setDigits_snoc (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (d : ℕ) (base : Tape u Extra → List Bool) :
    setDigits m (Fin.snoc digits d) base =
      putDigit ⟨q, hq⟩ (setDigits m digits base) d (m - 1 - d) := by
  funext k
  cases k with
  | current i =>
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
        hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
          hi, hi', hne]
  | remaining i =>
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
        hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
          hi, hi', hne]
  | _ => simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

theorem setDigits_snoc_base (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (d : ℕ) (base : Tape u Extra → List Bool) :
    setDigits m digits (putDigit ⟨q, hq⟩ base d (m - 1 - d)) =
      setDigits m (Fin.snoc digits d) base := by
  rw [setDigits_putDigit, setDigits_snoc]

def allBits {q : ℕ} (bits : (Fin q → Fin m) → List Bool) : List Bool :=
  (tupleOrder m q).flatMap bits

def blockPrefix (blocks : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => blockPrefix blocks n ++ blocks n

theorem blockPrefix_eq_ofFn (blocks : ℕ → List Bool) (n : ℕ) :
    blockPrefix blocks n = (List.ofFn (fun i : Fin n => blocks i.val)).flatten := by
  induction n with
  | zero => simp [blockPrefix]
  | succ n ih =>
    rw [blockPrefix, List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simpa only [Fin.val_castSucc, Fin.val_last, List.flatten_cons,
      List.flatten_nil, List.append_nil] using congrArg (fun xs => xs ++ blocks n) ih

def blocks {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) (d : ℕ) : List Bool :=
  if h : d < m then allBits (fun c => bits (Fin.snoc c ⟨d, h⟩)) else []

theorem blockPrefix_all {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) :
    blockPrefix (blocks bits) m = allBits bits := by
  rw [blockPrefix_eq_ofFn]
  simp only [blocks, Fin.isLt, ↓reduceDIte, allBits, tupleOrder_snoc]
  simp only [List.flatMap_assoc, List.flatMap_map]
  simp only [List.flatMap_def, List.map_ofFn, Function.comp_def]

def configuration (label : Λ) (canonical : σ) (tapes : Tape u Extra → List Bool) :
    Configuration (Tape u Extra) Λ σ := ⟨some label, (canonical, none), tapes⟩

def BodyTrace (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel returnLabel : Λ) (canonical : σ) (accumulator : Extra)
    {q : ℕ} (base : Tape u Extra → List Bool)
    (bits : (Fin q → Fin m) → List Bool) (B : ℕ) : Prop :=
  ∀ c output, ∃ count, count ≤ B ∧ (MachineComposition.advance (TM2.step program))^[count]
    (some (configuration bodyLabel canonical
      (setDigits m (fun i => (c i).val) (setAcc accumulator base output)))) =
    some (configuration returnLabel canonical
      (setDigits m (fun i => (c i).val)
        (setAcc accumulator base ((bits c).reverse ++ output))))

theorem val_snoc {q : ℕ} (c : Fin q → Fin m) (d : Fin m) :
    (fun i : Fin (q + 1) => (Fin.snoc (α := fun _ => Fin m) c d i).val) =
      Fin.snoc (fun i => (c i).val) d.val := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem zeros_snoc (q : ℕ) :
    Fin.snoc (fun _ : Fin q => (0 : ℕ)) 0 = fun _ : Fin (q + 1) => 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

def initialConfiguration (q : ℕ) (bodyLabel : Λ) (canonical : σ)
    (base : Tape u Extra → List Bool) : Configuration (Tape u Extra) Λ σ :=
  configuration bodyLabel canonical (setDigits m (fun _ : Fin q => 0) base)

def finalConfiguration {q : ℕ} (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (base : Tape u Extra → List Bool) (bits : (Fin q → Fin m) → List Bool) :
    Configuration (Tape u Extra) Λ σ :=
  configuration exitLabel canonical (setDigits m (fun _ : Fin q => 0)
    (setAcc accumulator base ((allBits bits).reverse ++ base (.extra accumulator))))

theorem exists_schedule
    (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ) (accumulator : Extra)
    (positive : 0 < m) (B q : ℕ) (hq : q ≤ u)
    (base : Tape u Extra → List Bool) (bits : (Fin q → Fin m) → List Bool)
    (atCheck : ∀ i, i < q → program (next i) =
      increment (currentAt accumulator i) (remainingAt accumulator i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < q → program (resetLabel i) =
      reset (currentAt accumulator i) (remainingAt accumulator i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical accumulator base bits B) :
    ∃ tree : NestedCycle m (currentAt accumulator) (remainingAt accumulator) bodyLabel
        next resetLabel program q (next q)
        (initialConfiguration (m := m) q bodyLabel canonical base)
        (finalConfiguration (next q) canonical accumulator base bits), tree.LeafBound B := by
  classical
  induction q generalizing base with
  | zero =>
    let empty : Fin 0 → Fin m := fun i => Fin.elim0 i
    obtain ⟨count, hcount, run⟩ := bodies empty (base (.extra accumulator))
    have hrun : (MachineComposition.advance (TM2.step program))^[count]
        (some (initialConfiguration (m := m) 0 bodyLabel canonical base)) =
        some (finalConfiguration (next 0) canonical accumulator base bits) := by
      simpa only [initialConfiguration, finalConfiguration, allBits,
        tupleOrder_dimension_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        setDigits_zero, setAcc_self] using run
    let tree := NestedCycle.leaf (n := m) (current := currentAt accumulator)
      (remaining := remainingAt accumulator) (bodyLabel := bodyLabel)
      (checkLabel := next) (resetLabel := resetLabel) (program := program)
      (next 0) (initialConfiguration (m := m) 0 bodyLabel canonical base)
      (finalConfiguration (next 0) canonical accumulator base bits) count rfl rfl hrun
    refine ⟨tree, ?_⟩
    dsimp only [tree]
    erw [NestedCycle.LeafBound]
    exact hcount
  | succ q ih =>
    have hqu : q < u := by omega
    let s : CycleSchedule (Tape u Extra) σ := {
      currentSuffix := []
      remainingSuffix := []
      ambient := fun _ => canonical
      register := fun _ => none
      base := fun r => setDigits m (fun _ : Fin q => 0)
        (setAcc accumulator base
          ((blockPrefix (blocks bits) (m - r)).reverse ++ base (.extra accumulator))) }
    have childrenExist (r : Fin m) :
        ∃ tree : NestedCycle m (currentAt accumulator) (remainingAt accumulator) bodyLabel
            next resetLabel program q (next q)
            (bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
              bodyLabel (m - 1) r.val s.currentSuffix s.remainingSuffix s.ambient s.base)
            (checkConfiguration (currentAt accumulator q) (remainingAt accumulator q)
              (next q) (m - 1) r.val s.currentSuffix s.remainingSuffix
              s.ambient s.register s.base), tree.LeafBound B := by
      let d : Fin m := NestedCycle.reverseDigit r
      let childBits : (Fin q → Fin m) → List Bool := fun c => bits (Fin.snoc c d)
      let childBase := putDigit ⟨q, hqu⟩
        (setAcc accumulator base
          ((blockPrefix (blocks bits) (m - (r.val + 1))).reverse ++ base (.extra accumulator)))
        d.val (m - 1 - d.val)
      have hrem : m - 1 - d.val = r.val := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hbefore : m - (r.val + 1) = d.val := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hafter : m - r.val = d.val + 1 := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hprefix : blockPrefix (blocks bits) (m - r.val) =
          blockPrefix (blocks bits) (m - (r.val + 1)) ++ allBits childBits := by
        rw [hafter, hbefore, blockPrefix]
        simp only [blocks, d.isLt, ↓reduceDIte, childBits]
      have childBodies : BodyTrace program bodyLabel (next 0) canonical accumulator
          childBase childBits B := by
        intro c output
        obtain ⟨count, hcount, h⟩ := bodies (Fin.snoc c d) output
        refine ⟨count, hcount, ?_⟩
        simpa only [childBase, childBits, ← putDigit_setAcc,
          setAcc_setAcc, setDigits_snoc_base, ← val_snoc] using h
      have lower := ih (by omega) childBase childBits
        (fun i hi => atCheck i (by omega)) (fun i hi => atReset i (by omega))
        childBodies
      have hstart : initialConfiguration (m := m) q bodyLabel canonical childBase =
          bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
            bodyLabel (m - 1) r.val s.currentSuffix s.remainingSuffix s.ambient s.base := by
        simp only [initialConfiguration, configuration, bodyConfiguration, s, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, setDigits_putDigit, hrem]
        rfl
      have hfinish : finalConfiguration (next q) canonical accumulator childBase childBits =
          checkConfiguration (currentAt accumulator q) (remainingAt accumulator q)
            (next q) (m - 1) r.val s.currentSuffix s.remainingSuffix
            s.ambient s.register s.base := by
        simp only [finalConfiguration, configuration, checkConfiguration, s, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, putDigit_extra, setAcc_apply,
          ← putDigit_setAcc, setAcc_setAcc, setDigits_putDigit, hrem, hprefix,
          List.reverse_append, List.append_assoc]
        rfl
      rw [hstart, hfinish] at lower
      exact lower
    let children := fun r : Fin m => Classical.choose (childrenExist r)
    let tree := NestedCycle.node q (next (q + 1)) positive
      (by simp [currentAt, remainingAt, hqu])
      (atCheck q (by omega)) (atReset q (by omega)) s children
    have hbounded : tree.LeafBound B := by
      simp only [tree, NestedCycle.LeafBound]
      intro r
      exact Classical.choose_spec (childrenExist r)
    have hstart : bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
        bodyLabel (m - 1) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base =
        initialConfiguration (m := m) (q + 1) bodyLabel canonical base := by
      have hm : m - 1 + 1 = m := by omega
      simp only [bodyConfiguration, initialConfiguration, configuration, s,
        currentAt, remainingAt, hqu, ↓reduceDIte, Nat.sub_self, hm,
        blockPrefix, List.reverse_nil, List.nil_append, setAcc_self]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have hfinish : cycleExit (currentAt accumulator q) (remainingAt accumulator q)
        (next (q + 1)) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base =
        finalConfiguration (next (q + 1)) canonical accumulator base bits := by
      simp only [cycleExit, finalConfiguration, configuration, s, currentAt, remainingAt,
        hqu, ↓reduceDIte, Nat.sub_zero, blockPrefix_all]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have result := (show ∃ t : NestedCycle m (currentAt accumulator) (remainingAt accumulator)
        bodyLabel next resetLabel program (q + 1) (next (q + 1))
        (bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
          bodyLabel (m - 1) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base)
        (cycleExit (currentAt accumulator q) (remainingAt accumulator q)
          (next (q + 1)) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base),
        t.LeafBound B from ⟨tree, hbounded⟩)
    rw [hstart, hfinish] at result
    exact result

/-- The time bound is derived from the concrete schedule, not from the number
of tuples alone. Dimension zero consists of its single actual body trace. -/
theorem traversalInTime
    (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ) (accumulator : Extra)
    (positive : 0 < m) (B : ℕ) (base : Tape u Extra → List Bool)
    (bits : (Fin u → Fin m) → List Bool)
    (atCheck : ∀ i, i < u → program (next i) =
      increment (currentAt accumulator i) (remainingAt accumulator i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < u → program (resetLabel i) =
      reset (currentAt accumulator i) (remainingAt accumulator i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical accumulator base bits B) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step program)
      (initialConfiguration (m := m) u bodyLabel canonical base)
      (some (finalConfiguration (next u) canonical accumulator base bits))
      ((B + 2 * u) * m ^ u)) := by
  obtain ⟨tree, ht⟩ := exists_schedule program bodyLabel next resetLabel canonical accumulator
    positive B u (Nat.le_refl _) base bits atCheck atReset bodies
  exact ⟨{
    steps := tree.steps
    evals_in_steps := tree.trace
    steps_le_m := tree.steps_le_power positive B ht }⟩

omit [DecidableEq Extra] in
@[simp] theorem initial_current (base : Tape u Extra → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin u) :
    (initialConfiguration (m := m) u bodyLabel canonical base).stk (.current i) =
      encodeWord 0 := by simp [initialConfiguration, configuration, setDigits]

omit [DecidableEq Extra] in
@[simp] theorem initial_remaining (base : Tape u Extra → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin u) :
    (initialConfiguration (m := m) u bodyLabel canonical base).stk (.remaining i) =
      encodeWord (m - 1) := by simp [initialConfiguration, configuration, setDigits]

@[simp] theorem final_current (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) (i : Fin u) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.current i) =
      encodeWord 0 := by simp [finalConfiguration, configuration, setDigits]

@[simp] theorem final_remaining (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) (i : Fin u) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.remaining i) =
      encodeWord (m - 1) := by simp [finalConfiguration, configuration, setDigits]

@[simp] theorem final_accumulator (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.extra accumulator) =
      ((tupleOrder m u).flatMap bits).reverse ++ base (.extra accumulator) := by
  simp [finalConfiguration, configuration, allBits]

end MaxCutGames.Foundations.Hastad.SourceOdometerSchedule

end OAI
