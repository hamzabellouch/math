import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachinePreservingLookupClean

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

namespace DFVSGames.Foundations.Complexity.MachineTableRows

open Turing
open PCP.GraphTables

inductive Label
  | relationRead | relationRestore | reverseRead | reverseRestore
  | tailRead | tailRestore | appendOld | appendRow | appendBack
  deriving DecidableEq

instance : Fintype Label := derive_fintype% Label

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def routine (fields : Fin 3 → K) (row output scratch : K)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .relationRead => Reduction.MachineTransfer.loopAt (fields 2) scratch id false
      (labels .relationRead) (some (labels .relationRestore))
  | .relationRestore => MachineCopy.forkLoop scratch (fields 2) row false
      (labels .relationRestore) (some (labels .reverseRead))
  | .reverseRead => Reduction.MachineTransfer.loopAt (fields 1) scratch id false
      (labels .reverseRead) (some (labels .reverseRestore))
  | .reverseRestore => MachineCopy.forkLoop scratch (fields 1) row false
      (labels .reverseRestore) (some (labels .tailRead))
  | .tailRead => Reduction.MachineTransfer.loopAt (fields 0) scratch id false
      (labels .tailRead) (some (labels .tailRestore))
  | .tailRestore => MachineCopy.forkLoop scratch (fields 0) row false
      (labels .tailRestore) (some (labels .appendOld))
  | .appendOld => Reduction.MachineTransfer.loopAt output scratch id false
      (labels .appendOld) (some (labels .appendRow))
  | .appendRow => Reduction.MachineTransfer.loopAt row scratch id false
      (labels .appendRow) (some (labels .appendBack))
  | .appendBack => Reduction.MachineTransfer.loopAt scratch output id false
      (labels .appendBack) exit

def fieldBits (fields : Fin 3 → K) (base : K → List Bool) : List Bool :=
  base (fields 0) ++ base (fields 1) ++ base (fields 2)

def fieldSize (fields : Fin 3 → K) (base : K → List Bool) : Nat :=
  (base (fields 0)).length + (base (fields 1)).length + (base (fields 2)).length

omit [DecidableEq K] in
@[simp] theorem fieldBits_length (fields : Fin 3 → K) (base : K → List Bool) :
    (fieldBits fields base).length = fieldSize fields base := by
  simp [fieldBits, fieldSize, Nat.add_assoc]

def prefixTapes (fields : Fin 3 → K) (row : K) (base : K → List Bool) : K → List Bool :=
  Function.update base row (fieldBits fields base ++ base row)

theorem prefixTrace (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowScratch : row ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hscratch : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * (fieldSize fields base + 3)]
      (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
      some ⟨some (labels .appendOld), (ambient, none), prefixTapes fields row base⟩ := by
  let afterRelation := Function.update base row (base (fields 2) ++ base row)
  let afterReverse := Function.update afterRelation row
    (base (fields 1) ++ afterRelation row)
  have hfirst := MachineCopy.copyTrace (fields 2) row scratch
    (hfields 2).1 (hfields 2).2 hrowScratch false
    (labels .relationRead) (labels .relationRestore) (some (labels .reverseRead))
    program (hprogram .relationRead) (hprogram .relationRestore) base hscratch ambient register
  change (MachineComposition.advance (TM2.step program))^[2 * ((base (fields 2)).length + 1)]
    (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
    some ⟨some (labels .reverseRead), (ambient, none), afterRelation⟩ at hfirst
  have hsecond := MachineCopy.copyTrace (fields 1) row scratch
    (hfields 1).1 (hfields 1).2 hrowScratch false
    (labels .reverseRead) (labels .reverseRestore) (some (labels .tailRead))
    program (hprogram .reverseRead) (hprogram .reverseRestore) afterRelation
    (by simp [afterRelation, Ne.symm hrowScratch, hscratch]) ambient none
  have hrev : afterRelation (fields 1) = base (fields 1) := by
    simp [afterRelation, (hfields 1).1]
  rw [hrev] at hsecond
  change (MachineComposition.advance (TM2.step program))^[2 * ((base (fields 1)).length + 1)]
    (some ⟨some (labels .reverseRead), (ambient, none), afterRelation⟩) =
    some ⟨some (labels .tailRead), (ambient, none), afterReverse⟩ at hsecond
  have hthird := MachineCopy.copyTrace (fields 0) row scratch
    (hfields 0).1 (hfields 0).2 hrowScratch false
    (labels .tailRead) (labels .tailRestore) (some (labels .appendOld))
    program (hprogram .tailRead) (hprogram .tailRestore) afterReverse
    (by simp [afterReverse, afterRelation, Ne.symm hrowScratch, hscratch]) ambient none
  have htail : afterReverse (fields 0) = base (fields 0) := by
    simp [afterReverse, afterRelation, (hfields 0).1]
  rw [htail] at hthird
  have hfinal : Function.update afterReverse row
      (base (fields 0) ++ afterReverse row) = prefixTapes fields row base := by
    simp [afterReverse, afterRelation, prefixTapes, fieldBits, List.append_assoc]
  rw [hfinal] at hthird
  rw [show 2 * (fieldSize fields base + 3) =
    2 * ((base (fields 0)).length + 1) +
      (2 * ((base (fields 1)).length + 1) + 2 * ((base (fields 2)).length + 1)) by
        simp only [fieldSize]; omega,
    Function.iterate_add_apply,
    Function.iterate_add_apply (m := 2 * ((base (fields 1)).length + 1))
      (n := 2 * ((base (fields 2)).length + 1)), hfirst, hsecond]
  exact hthird

theorem appendTrace (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowOutput : row ≠ output) (hrowScratch : row ≠ scratch)
    (houtputScratch : output ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hrow : base row = []) (hscratch : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[
        4 * fieldSize fields base + 2 * (base output).length + 9]
      (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base output (base output ++ fieldBits fields base)⟩ := by
  have hprefix := prefixTrace fields row output scratch hfields hrowScratch
    labels exit program hprogram base hscratch ambient register
  have happend := MachineAppendAt.appendTrace row output scratch hrowOutput hrowScratch
    houtputScratch false (labels .appendOld) (labels .appendRow) (labels .appendBack)
    exit program (hprogram .appendOld) (hprogram .appendRow) (hprogram .appendBack)
    (prefixTapes fields row base)
    (by simp [prefixTapes, Ne.symm hrowScratch, hscratch]) ambient none
  have hrowbits : prefixTapes fields row base row = fieldBits fields base := by
    simp [prefixTapes, hrow]
  have hout : prefixTapes fields row base output = base output := by
    simp [prefixTapes, Ne.symm hrowOutput]
  rw [hrowbits, hout, fieldBits_length] at happend
  have hfinal : MachineAppendAt.appendTapes row output (prefixTapes fields row base) =
      Function.update base output (base output ++ fieldBits fields base) := by
    funext k
    by_cases ho : k = output
    · subst k
      simp [MachineAppendAt.appendTapes, hrowbits, hout]
    · by_cases hr : k = row
      · subst k
        simp [MachineAppendAt.appendTapes, Reduction.MachineTransfer.tapesAt,
          prefixTapes, hrowOutput, hrow]
      · simp [MachineAppendAt.appendTapes, Reduction.MachineTransfer.tapesAt,
          prefixTapes, ho, hr]
  rw [hfinal] at happend
  rw [show 4 * fieldSize fields base + 2 * (base output).length + 9 =
      (2 * (fieldSize fields base + (base output).length) + 3) +
        2 * (fieldSize fields base + 3) by omega,
    Function.iterate_add_apply, hprefix]
  exact happend

theorem rowBits_eq {n m : Nat} (r : DartRow n m) :
    encodeWords (rowWords r) = encodeWord r.tail.val ++
      encodeWord r.reverseIndex.val ++ encodeWords (relationWords r.relation) := by
  simp [rowWords, encodeWords]

omit [DecidableEq K] in
theorem fieldBits_eq_rowBits {n m : Nat} (r : DartRow n m)
    (fields : Fin 3 → K) (base : K → List Bool)
    (htail : base (fields 0) = encodeWord r.tail.val)
    (hreverse : base (fields 1) = encodeWord r.reverseIndex.val)
    (hrelation : base (fields 2) = encodeWords (relationWords r.relation)) :
    fieldBits fields base = encodeWords (rowWords r) := by
  rw [fieldBits, htail, hreverse, hrelation, rowBits_eq]

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 9

omit [DecidableEq K] in
theorem timePolynomial_bounds (fields : Fin 3 → K) (base : K → List Bool) (output : K) :
    4 * fieldSize fields base + 2 * (base output).length + 9 ≤
      timePolynomial.eval (fieldSize fields base + (base output).length) := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  omega

def rowAppendInTime {n m : Nat} (r : DartRow n m)
    (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowOutput : row ≠ output) (hrowScratch : row ≠ scratch)
    (houtputScratch : output ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hrow : base row = []) (hscratch : base scratch = [])
    (htail : base (fields 0) = encodeWord r.tail.val)
    (hreverse : base (fields 1) = encodeWord r.reverseIndex.val)
    (hrelation : base (fields 2) = encodeWords (relationWords r.relation))
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .relationRead), (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base output (base output ++ encodeWords (rowWords r))⟩)
      (timePolynomial.eval (fieldSize fields base + (base output).length)) where
  steps := 4 * fieldSize fields base + 2 * (base output).length + 9
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[_] _ = _
    rw [← fieldBits_eq_rowBits r fields base htail hreverse hrelation]
    exact appendTrace fields row output scratch hfields hrowOutput hrowScratch
      houtputScratch labels exit program hprogram base hrow hscratch ambient register
  steps_le_m := timePolynomial_bounds fields base output

def machine : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Label
  main := .relationRead
  σ := Unit × Option Bool
  initialState := ((), none)
  m := routine (fun i : Fin 3 => i.castLE (by decide)) 3 4 5 id none

def machineRowInTime {n m : Nat} (r : DartRow n m) (base : Fin 6 → List Bool)
    (hrow : base 3 = []) (hscratch : base 5 = [])
    (htail : base 0 = encodeWord r.tail.val)
    (hreverse : base 1 = encodeWord r.reverseIndex.val)
    (hrelation : base 2 = encodeWords (relationWords r.relation)) (register : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some .relationRead, ((), register), base⟩
      (some ⟨none, ((), none),
        Function.update base (4 : Fin 6) (base 4 ++ encodeWords (rowWords r))⟩)
      (timePolynomial.eval ((encodeWords (rowWords r)).length + (base 4).length)) := by
  let fields : Fin 3 → Fin 6 := fun i => i.castLE (by decide)
  have hfields (i : Fin 3) : fields i ≠ 3 ∧ fields i ≠ 5 := by
    constructor
    · intro h
      have he := congrArg Fin.val h
      change i.val = 3 at he
      omega
    · intro h
      have he := congrArg Fin.val h
      change i.val = 5 at he
      omega
  have hsize : fieldSize fields base = (encodeWords (rowWords r)).length := by
    rw [← fieldBits_length, fieldBits_eq_rowBits r fields base htail hreverse hrelation]
  have run := rowAppendInTime r fields (3 : Fin 6) 4 5 hfields (by decide) (by decide)
    (by decide) id none machine.m (fun _ => rfl) base hrow hscratch
    htail hreverse hrelation () register
  rw [hsize] at run
  convert run using 1 ; rfl

theorem outputFrame (base : K → List Bool) (output k : K) (hk : k ≠ output)
    (bits : List Bool) :
    Function.update base output (base output ++ bits) k = base k := by
  simp [hk]

end DFVSGames.Foundations.Complexity.MachineTableRows

end

section

namespace DFVSGames.Foundations.Complexity.MachineRegularOriginalRow

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingRegularTables

def inheritedIndex (_H : BaseTable) (t : Table) (e : Fin t.darts) :
    Fin (vertexCount t (padding t) * (internalDegree + 1)) :=
  PortTables.rowIndex _ _
    (vertexOrder t (padding t) (.inl e), portOrder internalDegree (.inr ()))

def inheritedRow (H : BaseTable) (t : Table) (e : Fin t.darts) :
    DartRow (vertexCount t (padding t))
      (vertexCount t (padding t) * (internalDegree + 1)) :=
  (PortTables.flatRows (regularize H t))[inheritedIndex H t e]

theorem inheritedRow_eq (H : BaseTable) (t : Table) (e : Fin t.darts) :
    inheritedRow H t e =
      ⟨((PortTables.rowIndex _ _).symm (inheritedIndex H t e)).1,
        (regularize H t).reverseIndex[inheritedIndex H t e],
        (regularize H t).relations[inheritedIndex H t e]⟩ := by
  simp only [inheritedRow, PortTables.flatRows, Fin.getElem_fin,
    Vector.getElem_ofFn, Fin.eta]

@[simp] theorem inheritedRow_tail (H : BaseTable) (t : Table) (e : Fin t.darts) :
    (inheritedRow H t e).tail.val = e.val := by
  simp only [inheritedRow_eq, inheritedIndex, Equiv.symm_apply_apply,
    vertexOrder_original]

@[simp] theorem inheritedRow_reverse (H : BaseTable) (t : Table) (e : Fin t.darts) :
    (inheritedRow H t e).reverseIndex.val =
      (internalDegree + 1) * t.rows[e].reverseIndex.val + internalDegree := by
  rw [inheritedRow_eq]
  change ((regularize H t).reverseIndex[PortTables.rowIndex _ _
    (vertexOrder t (padding t) (.inl e), portOrder internalDegree (.inr ()))]).val = _
  rw [← PortTables.rowIndex_rotation, regularize, rotation_ofCloudTables]
  change (PortTables.rowIndex _ _
    (vertexOrder t (padding t) (.inl (reverseAt t.rows e)),
      portOrder internalDegree (.inr ()))).val = _
  rw [PortTables.rowIndex_val, vertexOrder_original, portOrder_inherited]
  exact Nat.add_comm _ _

@[simp] theorem inheritedRow_relation (H : BaseTable) (t : Table) (e : Fin t.darts) :
    (inheritedRow H t e).relation = t.rows[e].relation := by
  rw [inheritedRow_eq]
  apply Vector.ext
  intro i hi
  let j : Fin 4096 := ⟨i, hi⟩
  let ab := relationIndex.symm j
  have h := accepts_original t (padding t) (familyCloudTable H t) e ab.1 ab.2
  change relationAt ((regularize H t).relations[inheritedIndex H t e]) ab.1 ab.2 =
    relationAt t.rows[e].relation ab.1 ab.2 at h
  have hj : relationIndex (ab.1, ab.2) = j := relationIndex.apply_symm_apply j
  simpa only [relationAt, hj, Fin.getElem_fin, j] using h

theorem inheritedRow_words (H : BaseTable) (t : Table) (e : Fin t.darts) :
    rowWords (inheritedRow H t e) = e.val ::
      ((internalDegree + 1) * t.rows[e].reverseIndex.val + internalDegree) ::
        relationWords t.rows[e].relation := by
  simp only [rowWords, inheritedRow_tail, inheritedRow_reverse, inheritedRow_relation,
    List.cons_append, List.nil_append]

def prefixWords (t : Table) (e : Fin t.darts) : List Nat :=
  [t.vertices, t.darts] ++ ((rowList t).take e.val).flatMap rowWords

def suffixWords (t : Table) (e : Fin t.darts) : List Nat :=
  ((rowList t).drop (e.val + 1)).flatMap rowWords

theorem prefixWords_length (t : Table) (e : Fin t.darts) :
    (prefixWords t e).length = 2 + 4098 * e.val := by
  simp only [prefixWords, List.length_append, List.length_cons, List.length_nil,
    rowsWords_length, List.length_take, rowList_length, Nat.min_eq_left e.isLt.le]

theorem tableWords_at_row (t : Table) (e : Fin t.darts) :
    GraphTables.tableWords t = prefixWords t e ++ (rowWords t.rows[e] ++ suffixWords t e) := by
  have he : e.val < (rowList t).length := by simpa only [rowList_length] using e.isLt
  have hs : (rowList t).take e.val ++ (rowList t)[e.val] ::
      (rowList t).drop (e.val + 1) = rowList t := by
    rw [List.getElem_cons_drop he, List.take_append_drop]
  have hw := congrArg (fun rs : List (DartRow t.vertices t.darts) => rs.flatMap rowWords) hs
  simp only [List.flatMap_append, List.flatMap_cons, rowList, Vector.getElem_toList] at hw
  unfold GraphTables.tableWords prefixWords suffixWords rowList
  rw [← hw]
  simp only [List.append_assoc, Fin.getElem_fin]

theorem tableWords_drop_row (t : Table) (e : Fin t.darts) :
    (GraphTables.tableWords t).drop (2 + 4098 * e.val) = rowWords t.rows[e] ++ suffixWords t e := by
  rw [tableWords_at_row]
  exact List.drop_left' (l₂ := rowWords t.rows[e] ++ suffixWords t e)
    (prefixWords_length t e)

theorem selected_reverse (t : Table) (e : Fin t.darts) :
    (GraphTables.tableWords t)[4098 * e.val + 3]? = some t.rows[e].reverseIndex.val := by
  have h := congrArg (fun words : List Nat => words[1]?) (tableWords_drop_row t e)
  simp only [List.getElem?_drop] at h
  rw [show 2 + 4098 * e.val + 1 = 4098 * e.val + 3 by omega] at h
  simpa [rowWords] using h

theorem remaining_relation (t : Table) (e : Fin t.darts) :
    (GraphTables.tableWords t).drop (4098 * e.val + 3 + 1) =
      relationWords t.rows[e].relation ++ suffixWords t e := by
  rw [show 4098 * e.val + 3 + 1 = (2 + 4098 * e.val) + 2 by omega,
    ← List.drop_drop, tableWords_drop_row]
  simp only [rowWords, List.cons_append, List.drop_succ_cons, List.drop_zero, List.nil_append]

abbrev Tape := Fin 10
abbrev Buffer := MachineFixedBlockMap.Buffer 4096
abbrev State (σ : Type) := (σ × Buffer) × Option Bool
abbrev Alphabet (_ : Tape) := Bool

def zeroBuffer : Buffer := MachineFixedBlockMap.emptyBuffer 4096

def lookupTape (i : Fin 5) : Tape := ⟨i.val + 1, by omega⟩

theorem lookupTape_injective : Function.Injective lookupTape := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [lookupTape] at hv
  omega

theorem source_outside (i : Fin 5) : (0 : Tape) ≠ lookupTape i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [lookupTape] at hv
  omega

def fields : Fin 3 → Tape := Fin.cases 0 (Fin.cases 6 (fun _ => 7))

@[simp] theorem fields_zero : fields 0 = 0 := rfl
@[simp] theorem fields_one : fields 1 = 6 := rfl
@[simp] theorem fields_two : fields 2 = 7 := rfl

theorem fields_separate (i : Fin 3) : fields i ≠ 8 ∧ fields i ≠ 5 := by
  fin_cases i <;> decide

def copyStateEquiv (σ : Type) : ((σ × Option Bool) × Buffer) ≃ State σ where
  toFun s := ((s.1.1, s.2), s.1.2)
  invFun s := ((s.1.1, s.2), s.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

inductive Label
  | lookup (label : MachineAffineLookup.Label)
  | copyRelation | reverseSeed | reverseScan | reverseRestore
  | emit (label : MachineTableRows.Label)
  deriving DecidableEq, Fintype

def relationCopyAt {K σ Λ : Type} (src dst : K) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State σ) :=
  MachineStateEquiv.statement (copyStateEquiv σ)
    (PoweringMachineRow.encodedBlockAt src dst (id : Buffer → Buffer) exit)

def instruction {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ (State σ)
  | .lookup l => MachineAffineLookup.instruction 0 lookupTape 4098 3
      (fun l => labels (.lookup l)) (some (labels .copyRelation)) l
  | .copyRelation => relationCopyAt 3 7 (some (labels .reverseSeed))
  | .reverseSeed => MachineUnaryAffineAt.seed 6 q (labels .reverseScan)
  | .reverseScan => MachineUnaryAffineAt.scan 4 5 6 (q + 1)
      (labels .reverseScan) (labels .reverseRestore)
  | .reverseRestore => Reduction.MachineTransfer.loopAt 5 4 id false
      (labels .reverseRestore) (some (labels (.emit .relationRead)))
  | .emit l => MachineTableRows.routine fields 8 9 5 (fun l => labels (.emit l)) exit l

def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := 1
  k₁ := 9
  Γ := Alphabet
  Λ := Label
  main := .lookup .seed
  σ := State Unit
  initialState := (((), zeroBuffer), none)
  m := instruction q id none

def looked (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Tape → List Bool :=
  MachineAffineLookup.finalTapes lookupTape base (GraphTables.tableWords t) (4098 * e.val + 3)
    t.rows[e].reverseIndex.val

def copied (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (looked t e base) 3
    (encodeWords (suffixWords t e) ++ base 3)) 7
    (encodeWords (relationWords t.rows[e].relation) ++ base 7)

def affined (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    Tape → List Bool :=
  Function.update (copied t e base) 6
    (encodeWord ((q + 1) * t.rows[e].reverseIndex.val + q) ++ base 6)

theorem looked_other (t : Table) (e : Fin t.darts) (base : Tape → List Bool)
    (k : Tape) (h₂ : k ≠ 2) (h₃ : k ≠ 3) (h₄ : k ≠ 4) :
    looked t e base k = base k :=
  MachineAffineLookup.finalTapes_other lookupTape base _ _ _ k h₂ h₃ h₄

theorem looked_reverse (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    looked t e base 4 = encodeWord t.rows[e].reverseIndex.val ++ base 4 :=
  MachineAffineLookup.finalTapes_output lookupTape base _ _ _

theorem looked_relation (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    looked t e base 3 = encodeWords (relationWords t.rows[e].relation) ++
      (encodeWords (suffixWords t e) ++ base 3) := by
  change MachineLookup.tapes (2 : Tape) 3 4 base
    (encodeWord 0 ++ base 2)
    (encodeWords ((GraphTables.tableWords t).drop (4098 * e.val + 3 + 1)) ++ base 3)
    (encodeWord t.rows[e].reverseIndex.val ++ base 4) 3 = _
  rw [MachineLookup.tapes_source _ _ _ (by decide), remaining_relation, encodeWords_append]
  exact List.append_assoc _ _ _

theorem vectorBits_eq_encodedBlock {n : Nat} (relation : Vector Bool n) :
    PoweringMachineRow.encodeBits (List.ofFn (fun i : Fin n => relation[i])) =
      encodeWords (relation.toList.map GraphTables.bitWord) := by
  rw [PoweringMachineRow.encodeBits_graphWords]
  congr 1
  congr 1
  have hvec : Vector.ofFn (fun i : Fin n => relation[i]) = relation := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  exact Vector.toList_ofFn.symm.trans (congrArg Vector.toList hvec)

theorem relationBits_eq_encodedBlock (relation : RelationTable) :
    PoweringMachineRow.encodeBits (List.ofFn (fun i : Fin 4096 => relation[i])) =
      encodeWords (relationWords relation) := vectorBits_eq_encodedBlock relation

theorem relationCopy_step {K Λ σ : Type} [DecidableEq K]
    (src dst : K) (hne : src ≠ dst) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : program label = relationCopyAt src dst exit)
    (relation : RelationTable) (suffix : List Bool) (base : K → List Bool)
    (input : base src = encodeWords (relationWords relation) ++ suffix)
    (ambient : σ) (buffer : Buffer) (register : Option Bool) :
    TM2.step program ⟨some label, ((ambient, buffer), register), base⟩ =
      some ⟨exit, ((ambient, zeroBuffer), register),
        Function.update (Function.update base src suffix) dst
          (encodeWords (relationWords relation) ++ base dst)⟩ := by
  change some (TM2.stepAux (program label) _ base) = _
  rw [code]
  unfold relationCopyAt
  rw [MachineStateEquiv.stepAux_transport_symm]
  change some (MachineStateEquiv.configuration (copyStateEquiv σ)
    (TM2.stepAux (PoweringMachineRow.encodedBlockAt src dst (id : Buffer → Buffer) exit)
      ((ambient, register), buffer) base)) = _
  have hinput : base src = PoweringMachineRow.encodeBits
      (List.ofFn (fun i : Fin 4096 => relation[i])) ++ suffix := by
    rw [relationBits_eq_encodedBlock]
    exact input
  rw [PoweringMachineRow.stepAux_encodedBlockAt src dst (id : Buffer → Buffer)
    exit hne (fun i : Fin 4096 => relation[i]) suffix
    ((ambient, register), buffer) base hinput]
  simp only [id_eq, relationBits_eq_encodedBlock, MachineStateEquiv.configuration,
    copyStateEquiv, zeroBuffer]
  rfl

theorem relationCopy_pushBound {K Λ σ : Type} (src dst : K) (exit : Option Λ) :
    Runtime.statementPushBound (relationCopyAt (σ := σ) src dst exit) = 8192 := by
  rw [relationCopyAt, MachineStateEquiv.statementPushBound,
    PoweringMachineRow.statementPushBound_encodedBlockAt]

theorem copied_other (t : Table) (e : Fin t.darts) (base : Tape → List Bool)
    (k : Tape) (h₂ : k ≠ 2) (h₃ : k ≠ 3) (h₄ : k ≠ 4) (h₇ : k ≠ 7) :
    copied t e base k = base k := by
  simp only [copied, Function.update_of_ne h₇, Function.update_of_ne h₃,
    looked_other t e base k h₂ h₃ h₄]

theorem copied_reverse (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    copied t e base 4 = encodeWord t.rows[e].reverseIndex.val ++ base 4 := by
  simp only [copied, Function.update_of_ne (by decide : (4 : Tape) ≠ 7),
    Function.update_of_ne (by decide : (4 : Tape) ≠ 3), looked_reverse]

theorem copied_relation (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    copied t e base 7 = encodeWords (relationWords t.rows[e].relation) ++ base 7 := by
  simp only [copied, Function.update_self]

theorem affined_other (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool)
    (k : Tape) (h₂ : k ≠ 2) (h₃ : k ≠ 3) (h₄ : k ≠ 4) (h₆ : k ≠ 6) (h₇ : k ≠ 7) :
    affined q t e base k = base k := by
  simp only [affined, Function.update_of_ne h₆, copied_other t e base k h₂ h₃ h₄ h₇]

theorem affined_reverse (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    affined q t e base 6 = encodeWord ((q + 1) * t.rows[e].reverseIndex.val + q) ++ base 6 := by
  simp only [affined, Function.update_self]

theorem affined_relation (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    affined q t e base 7 = encodeWords (relationWords t.rows[e].relation) ++ base 7 := by
  simp only [affined, Function.update_of_ne (by decide : (7 : Tape) ≠ 6), copied_relation]

structure Input (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Prop where
  indexWord : base 0 = encodeWord e.val
  tableWord : base 1 = tableBits t
  reverseEmpty : base 4 = []
  scratchEmpty : base 5 = []
  computedEmpty : base 6 = []
  relationEmpty : base 7 = []
  rowEmpty : base 8 = []

def emittedWords (q : Nat) (t : Table) (e : Fin t.darts) : List Nat :=
  e.val :: ((q + 1) * t.rows[e].reverseIndex.val + q) :: relationWords t.rows[e].relation

theorem affined_fields (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    MachineTableRows.fieldBits fields (affined q t e base) = encodeWords (emittedWords q t e) := by
  have htail := affined_other q t e base 0 (by decide) (by decide) (by decide)
    (by decide) (by decide)
  simp only [MachineTableRows.fieldBits, fields_zero, fields_one, fields_two,
    htail, input.indexWord, affined_reverse, input.computedEmpty,
    affined_relation, input.relationEmpty, List.append_nil,
    emittedWords, encodeWords, List.append_assoc]

def rowSteps (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Nat :=
  4 * (encodeWords (emittedWords q t e)).length + 2 * (base 9).length + 9

def steps (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Nat :=
  MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 3 + 1 +
    (2 * (t.rows[e].reverseIndex.val + 1) + 1) + rowSteps q t e base

def finalTapes (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    Tape → List Bool :=
  Function.update (affined q t e base) 9 (base 9 ++ encodeWords (emittedWords q t e))

section Execution

variable {Λ σ : Type}

private theorem join_trace_inline_MachineRegularOriginalRow {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem lookupTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 3]
      (some ⟨some (labels (.lookup .seed)), ((ambient, zeroBuffer), register), base⟩) =
      some ⟨some (labels .copyRelation), ((ambient, zeroBuffer), none), looked t e base⟩ := by
  exact MachineAffineLookup.affineLookupTrace 0 lookupTape lookupTape_injective source_outside
    4098 3 (fun l => labels (.lookup l)) (some (labels .copyRelation)) program
    (fun l => code (.lookup l)) base (GraphTables.tableWords t) input.tableWord input.scratchEmpty
    e.val [] (by simpa only [List.append_nil] using input.indexWord)
    t.rows[e].reverseIndex.val (selected_reverse t e) (ambient, zeroBuffer) register

theorem copyTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (ambient : σ) :
    (advance (TM2.step program))^[1]
      (some ⟨some (labels .copyRelation), ((ambient, zeroBuffer), none), looked t e base⟩) =
      some ⟨some (labels .reverseSeed), ((ambient, zeroBuffer), none), copied t e base⟩ := by
  simp only [Function.iterate_one, advance_some]
  have run := relationCopy_step (3 : Tape) 7 (by decide) (labels .copyRelation)
    (some (labels .reverseSeed)) program (code .copyRelation) t.rows[e].relation
    (encodeWords (suffixWords t e) ++ base 3) (looked t e base) (looked_relation t e base)
    ambient zeroBuffer none
  rw [looked_other t e base 7 (by decide) (by decide) (by decide)] at run
  exact run

theorem affineTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) :
    (advance (TM2.step program))^[2 * (t.rows[e].reverseIndex.val + 1) + 1]
      (some ⟨some (labels .reverseSeed), ((ambient, zeroBuffer), none), copied t e base⟩) =
      some ⟨some (labels (.emit .relationRead)), ((ambient, zeroBuffer), none),
        affined q t e base⟩ := by
  have hsource : copied t e base 4 = encodeWord t.rows[e].reverseIndex.val ++ [] := by
    rw [copied_reverse, input.reverseEmpty]
  have hscratch : copied t e base 5 = [] := by
    rw [copied_other t e base 5 (by decide) (by decide) (by decide) (by decide), input.scratchEmpty]
  have run := MachineUnaryAffineAt.seededAffineTrace (4 : Tape) 5 6 (by decide) (by decide)
    (by decide) (q + 1) q (labels .reverseSeed) (labels .reverseScan) (labels .reverseRestore)
    (some (labels (.emit .relationRead))) program (code .reverseSeed) (code .reverseScan)
    (code .reverseRestore) (copied t e base) t.rows[e].reverseIndex.val [] hsource hscratch
    (ambient, zeroBuffer) none
  rw [copied_other t e base 6 (by decide) (by decide) (by decide) (by decide)] at run
  exact run

theorem emitTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) :
    (advance (TM2.step program))^[rowSteps q t e base]
      (some ⟨some (labels (.emit .relationRead)), ((ambient, zeroBuffer), none), affined q t e base⟩) =
      some ⟨exit, ((ambient, zeroBuffer), none), finalTapes q t e base⟩ := by
  have hrow : affined q t e base 8 = [] := by
    rw [affined_other q t e base 8 (by decide) (by decide) (by decide) (by decide)
      (by decide), input.rowEmpty]
  have hscratch : affined q t e base 5 = [] := by
    rw [affined_other q t e base 5 (by decide) (by decide) (by decide) (by decide)
      (by decide), input.scratchEmpty]
  have hout := affined_other q t e base 9 (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hfields := affined_fields q t e base input
  have hsize : MachineTableRows.fieldSize fields (affined q t e base) =
      (encodeWords (emittedWords q t e)).length := by
    rw [← MachineTableRows.fieldBits_length, hfields]
  have run := MachineTableRows.appendTrace fields (8 : Tape) 9 5 fields_separate
    (by decide) (by decide) (by decide) (fun l => labels (.emit l)) exit program
    (fun l => code (.emit l)) (affined q t e base) hrow hscratch (ambient, zeroBuffer) none
  rw [hsize, hout, hfields] at run
  exact run

theorem traceAt (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps q t e base]
      (some ⟨some (labels (.lookup .seed)), ((ambient, zeroBuffer), register), base⟩) =
      some ⟨exit, ((ambient, zeroBuffer), none), finalTapes q t e base⟩ := by
  have hlookup := lookupTrace q labels exit program code t e base input ambient register
  have hcopy := copyTrace q labels exit program code t e base ambient
  have haffine := affineTrace q labels exit program code t e base input ambient
  have hemit := emitTrace q labels exit program code t e base input ambient
  exact join_trace_inline_MachineRegularOriginalRow (join_trace_inline_MachineRegularOriginalRow (join_trace_inline_MachineRegularOriginalRow hlookup hcopy) haffine) hemit

end Execution

def timeBound (q inputLength outputLength : Nat) : Nat :=
  (4 * q + 17) * inputLength + 2 * outputLength + 4 * q + 32795

theorem steps_le (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    steps q t e base ≤ timeBound q (tableBits t).length (base 9).length := by
  have hl := MachineAffineLookup.steps_le (GraphTables.tableWords t) e.val 4098 3
    t.rows[e].reverseIndex.val (selected_reverse t e)
  have htable := tableWords_length_le_bits t
  have he : e.val ≤ (tableBits t).length := by have he := e.isLt; omega
  have hr : t.rows[e].reverseIndex.val ≤ (tableBits t).length := by
    have hrlt := t.rows[e].reverseIndex.isLt
    omega
  have hrel := relationBits_length_le t.rows[e].relation
  have hmul := Nat.mul_le_mul_left (4 * (q + 1) + 2) hr
  change MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 3 ≤
    2 * e.val + 5 * (tableBits t).length + 6 at hl
  unfold steps rowSteps timeBound emittedWords
  simp only [encodeWords, List.length_append, encodeWord_length]
  nlinarith

def machineInTime (H : BaseTable) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine internalDegree).step
      ⟨some (.lookup .seed), (((), zeroBuffer), register), base⟩
      (some ⟨none, (((), zeroBuffer), none),
        Function.update (affined internalDegree t e base) (9 : Tape)
          (base (9 : Tape) ++ encodeWords (rowWords (inheritedRow H t e)))⟩)
      (timeBound internalDegree (tableBits t).length (base (9 : Tape)).length) where
  steps := steps internalDegree t e base
  evals_in_steps := by
    change (advance (TM2.step (instruction internalDegree id none)))^[_] _ = _
    rw [inheritedRow_words]
    exact traceAt internalDegree id none (instruction internalDegree id none)
      (fun _ => rfl) t e base input () register
  steps_le_m := steps_le internalDegree t e base

end DFVSGames.Foundations.Complexity.MachineRegularOriginalRow
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
