import Mathlib.Tactic.FinCases
import OAI.Computability.BinPacking.Computation.PoweringGlobalEnumeration

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularOriginalRow

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

private theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
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
  exact join_trace (join_trace (join_trace hlookup hcopy) haffine) hemit

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

end BinPackingGames.Foundations.Complexity.MachineRegularOriginalRow

namespace BinPackingGames.Foundations.Complexity.MachineLazyRows

open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap moveRow moveRow_words)

variable {K Λ A : Type} [DecidableEq K]

abbrev Label (d : Nat) := MachinePortReindex.Label d ⊕ MachineTableRows.Label
abbrev State (A : Type) (d : Nat) := MachinePortReindex.State A d

def addressIndex : Fin 5 → Fin 9 := ![1, 3, 4, 5, 6]

theorem addressIndex_injective : Function.Injective addressIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [addressIndex]

def fields (tape : Fin 9 → K) : Fin 3 → K := ![tape 0, tape 6, tape 2]

def reindexInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 9 → K)
    (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (fun _ : K => Bool) Λ (State A d)
  | .inl stage => MachinePortReindex.instruction d positive c b
      (tape ∘ addressIndex) (fun stage => labels (.inl stage))
      (some (labels (.inr .relationRead))) stage
  | .inr stage => MachineTableRows.routine (fields tape) (tape 8) (tape 7) (tape 3)
      (fun stage => labels (.inr stage)) exit stage

def instruction (d : Nat) (positive : 0 < d) (tape : Fin 9 → K)
    (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (fun _ : K => Bool) Λ (State A d) :=
  reindexInstruction d positive (2 * d) d tape labels exit

def reindexRowBits (d c b v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord (MachinePortReindex.value d c b j) ++
    encodeWords (relationWords relation)

def reindexMappedTapes (d c b j : Nat) (tape : Fin 9 → K)
    (base : K → List Bool) : K → List Bool :=
  Function.update base (tape 6) (encodeWord (MachinePortReindex.value d c b j))

def reindexResultTapes (d c b v j : Nat) (relation : RelationTable)
    (tape : Fin 9 → K) (base : K → List Bool) : K → List Bool :=
  Function.update (reindexMappedTapes d c b j tape base) (tape 7)
    (base (tape 7) ++ reindexRowBits d c b v j relation)

def reindexSteps (d c b v j : Nat) (relation : RelationTable) (output : List Bool) : Nat :=
  MachinePortReindex.steps d j + 4 * (reindexRowBits d c b v j relation).length +
    2 * output.length + 9

def rowBits (d v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord (reverseMap d j) ++ encodeWords (relationWords relation)

def mappedTapes (d j : Nat) (tape : Fin 9 → K) (base : K → List Bool) : K → List Bool :=
  Function.update base (tape 6) (encodeWord (reverseMap d j))

def resultTapes (d v j : Nat) (relation : RelationTable)
    (tape : Fin 9 → K) (base : K → List Bool) : K → List Bool :=
  Function.update (mappedTapes d j tape base) (tape 7)
    (base (tape 7) ++ rowBits d v j relation)

def steps (d v j : Nat) (relation : RelationTable) (output : List Bool) : Nat :=
  MachinePortReindex.steps d j + 4 * (rowBits d v j relation).length + 2 * output.length + 9

theorem reindexRowTrace (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 9 → K)
    (distinct : Function.Injective tape) (labels : Label d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A d))
    (atLabels : ∀ l, program (labels l) = reindexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (v j : Nat) (relation : RelationTable)
    (tailWord : base (tape 0) = encodeWord v)
    (reverseWord : base (tape 1) = encodeWord j)
    (relationWord : base (tape 2) = encodeWords (relationWords relation))
    (scratchEmpty : base (tape 3) = []) (workEmpty : base (tape 4) = [])
    (quotientEmpty : base (tape 5) = []) (newReverseEmpty : base (tape 6) = [])
    (rowEmpty : base (tape 8) = []) (ambient : A) :
    (advance (TM2.step program))^[reindexSteps d c b v j relation (base (tape 7))]
      (some ⟨some (labels (.inl .copySeed)), MachinePortReindex.clean d positive ambient, base⟩) =
      some ⟨exit, MachinePortReindex.clean d positive ambient,
        reindexResultTapes d c b v j relation tape base⟩ := by
  have hd (i k : Fin 9) (h : i ≠ k) : tape i ≠ tape k := fun e => h (distinct e)
  have ha0 : addressIndex 0 = 1 := rfl
  have ha4 : addressIndex 4 = 6 := rfl
  have mapRun := MachinePortReindex.reindexTrace d positive c b
    (tape ∘ addressIndex) (distinct.comp addressIndex_injective)
    (fun stage => labels (.inl stage)) (some (labels (.inr .relationRead)))
    program (fun stage => atLabels (.inl stage)) base j []
    (by simpa only [Function.comp_apply, ha0, List.append_nil] using reverseWord)
    scratchEmpty workEmpty quotientEmpty ambient
  simp only [Function.comp_apply, ha4, newReverseEmpty,
    List.append_nil] at mapRun
  change (advance (TM2.step program))^[MachinePortReindex.steps d j]
    (some ⟨some (labels (.inl .copySeed)), MachinePortReindex.clean d positive ambient, base⟩) =
    some ⟨some (labels (.inr .relationRead)), MachinePortReindex.clean d positive ambient,
      reindexMappedTapes d c b j tape base⟩ at mapRun
  have hfields (i : Fin 3) : fields tape i ≠ tape 8 ∧ fields tape i ≠ tape 3 := by
    fin_cases i
    · exact ⟨hd 0 8 (by decide), hd 0 3 (by decide)⟩
    · exact ⟨hd 6 8 (by decide), hd 6 3 (by decide)⟩
    · exact ⟨hd 2 8 (by decide), hd 2 3 (by decide)⟩
  have hbits : MachineTableRows.fieldBits (fields tape) (reindexMappedTapes d c b j tape base) =
      reindexRowBits d c b v j relation := by
    simp [MachineTableRows.fieldBits, fields, reindexMappedTapes, hd 0 6 (by decide),
      hd 2 6 (by decide), tailWord, relationWord, reindexRowBits]
  have hsize : MachineTableRows.fieldSize (fields tape) (reindexMappedTapes d c b j tape base) =
      (reindexRowBits d c b v j relation).length := by
    rw [← MachineTableRows.fieldBits_length, hbits]
  have hout : reindexMappedTapes d c b j tape base (tape 7) = base (tape 7) := by
    simp [reindexMappedTapes, hd 7 6 (by decide)]
  have appendRun := MachineTableRows.appendTrace (fields tape) (tape 8) (tape 7) (tape 3)
    hfields (hd 8 7 (by decide)) (hd 8 3 (by decide)) (hd 7 3 (by decide))
    (fun stage => labels (.inr stage)) exit program
    (fun stage => atLabels (.inr stage)) (reindexMappedTapes d c b j tape base)
    (by simp [reindexMappedTapes, hd 8 6 (by decide), rowEmpty])
    (by simp [reindexMappedTapes, hd 3 6 (by decide), scratchEmpty])
    (ambient, MachineFixedDivMod.residue d positive 0) none
  rw [hsize, hout, hbits] at appendRun
  change (advance (TM2.step program))^[4 * (reindexRowBits d c b v j relation).length +
      2 * (base (tape 7)).length + 9]
    (some ⟨some (labels (.inr .relationRead)), MachinePortReindex.clean d positive ambient,
      reindexMappedTapes d c b j tape base⟩) =
    some ⟨exit, MachinePortReindex.clean d positive ambient,
      reindexResultTapes d c b v j relation tape base⟩ at appendRun
  rw [show reindexSteps d c b v j relation (base (tape 7)) =
      (4 * (reindexRowBits d c b v j relation).length + 2 * (base (tape 7)).length + 9) +
        MachinePortReindex.steps d j by unfold reindexSteps; omega,
    Function.iterate_add_apply, mapRun, appendRun]

theorem rowTrace (d : Nat) (positive : 0 < d) (tape : Fin 9 → K)
    (distinct : Function.Injective tape) (labels : Label d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A d))
    (atLabels : ∀ l, program (labels l) = instruction d positive tape labels exit l)
    (base : K → List Bool) (v j : Nat) (relation : RelationTable)
    (tailWord : base (tape 0) = encodeWord v)
    (reverseWord : base (tape 1) = encodeWord j)
    (relationWord : base (tape 2) = encodeWords (relationWords relation))
    (scratchEmpty : base (tape 3) = []) (workEmpty : base (tape 4) = [])
    (quotientEmpty : base (tape 5) = []) (newReverseEmpty : base (tape 6) = [])
    (rowEmpty : base (tape 8) = []) (ambient : A) :
    (advance (TM2.step program))^[steps d v j relation (base (tape 7))]
      (some ⟨some (labels (.inl .copySeed)), MachinePortReindex.clean d positive ambient, base⟩) =
      some ⟨exit, MachinePortReindex.clean d positive ambient,
        resultTapes d v j relation tape base⟩ := by
  simpa only [reindexSteps, reindexResultTapes, reindexMappedTapes, reindexRowBits,
    MachinePortReindex.lazy_value, reverseMap, steps, resultTapes, mappedTapes, rowBits] using
    reindexRowTrace d positive (2 * d) d tape distinct labels exit program atLabels
      base v j relation tailWord reverseWord relationWord scratchEmpty workEmpty
      quotientEmpty newReverseEmpty rowEmpty ambient

theorem rowBits_eq_moveRow {n d : Nat} (table : PCP.PortTables.Table n d)
    (v : Fin n) (p : Fin d) :
    rowBits d v.val (PCP.PreprocessingLazyWords.row table v p).reverseIndex.val
        (PCP.PreprocessingLazyWords.row table v p).relation =
      encodeWords (rowWords (moveRow table v p)) := by
  rw [moveRow_words]
  simp [rowBits, encodeWords]

def machine (d : Nat) (positive : 0 < d) : FinTM2 where
  K := Fin 9
  k₀ := 1
  k₁ := 7
  Γ _ := Bool
  Λ := Label d
  main := .inl .copySeed
  σ := State Unit d
  initialState := MachinePortReindex.clean d positive ()
  m := instruction d positive id id none

abbrev Buffer := MachineRegularOriginalRow.Buffer
abbrev StreamState (A : Type) (d : Nat) := State (A × Buffer) d

def streamClean (d : Nat) (positive : 0 < d) (ambient : A) : StreamState A d :=
  MachinePortReindex.clean d positive (ambient, MachineRegularOriginalRow.zeroBuffer)

def relationStateEquiv (A : Type) (d : Nat) :
    MachineRegularOriginalRow.State (A × Fin d) ≃ StreamState A d where
  toFun s := (((s.1.1.1, s.1.2), s.1.1.2), s.2)
  invFun s := (((s.1.1.1, s.1.2), s.1.1.2), s.2)
  left_inv _ := rfl
  right_inv _ := rfl

def streamRelationCopy (d : Nat) (source destination : K) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d) :=
  MachineStateEquiv.statement (relationStateEquiv A d)
    (MachineRegularOriginalRow.relationCopyAt source destination exit)

theorem streamRelationCopy_step (d : Nat) (positive : 0 < d)
    (source destination : K) (different : source ≠ destination)
    (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (code : program label = streamRelationCopy d source destination exit)
    (relation : RelationTable) (suffix : List Bool) (base : K → List Bool)
    (input : base source = encodeWords (relationWords relation) ++ suffix) (ambient : A) :
    TM2.step program ⟨some label, streamClean d positive ambient, base⟩ =
      some ⟨exit, streamClean d positive ambient,
        Function.update (Function.update base source suffix) destination
          (encodeWords (relationWords relation) ++ base destination)⟩ := by
  have hraw := MachineRegularOriginalRow.relationCopy_step source destination different label exit
    (fun _ => MachineRegularOriginalRow.relationCopyAt source destination exit) rfl
    relation suffix base input (ambient, MachineFixedDivMod.residue d positive 0)
    MachineRegularOriginalRow.zeroBuffer none
  have haux := Option.some.inj hraw
  change some (TM2.stepAux (program label) (streamClean d positive ambient) base) = _
  rw [code, streamRelationCopy, MachineStateEquiv.stepAux_transport_symm]
  change some (MachineStateEquiv.configuration (relationStateEquiv A d)
    (TM2.stepAux (MachineRegularOriginalRow.relationCopyAt source destination exit)
      (((ambient, MachineFixedDivMod.residue d positive 0),
        MachineRegularOriginalRow.zeroBuffer), none) base)) = _
  rw [haux]
  rfl

def bodyIndex (i : Fin 9) : Fin 10 := i.castSucc

theorem bodyIndex_injective : Function.Injective bodyIndex := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 10 => k.val) h

inductive StreamLabel (d : Nat)
  | tailStart | tailRead | reverseStart | reverseRead | copyRelation
  | row (stage : Label d)
  | clearTail | clearOld | clearRelation | clearNew
  deriving DecidableEq, Fintype

def streamInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (labels : StreamLabel d → Λ) (exit : Option Λ) :
    StreamLabel d → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d)
  | .tailStart => Hastad.SourceMachine.fieldStart (tape 0) (labels .tailRead)
  | .tailRead => Hastad.SourceMachine.fieldLoop (tape 9) (tape 0) (labels .tailRead)
      (some (labels .reverseStart))
  | .reverseStart => Hastad.SourceMachine.fieldStart (tape 1) (labels .reverseRead)
  | .reverseRead => Hastad.SourceMachine.fieldLoop (tape 9) (tape 1) (labels .reverseRead)
      (some (labels .copyRelation))
  | .copyRelation => streamRelationCopy d (tape 9) (tape 2)
      (some (labels (.row (.inl .copySeed))))
  | .row stage => reindexInstruction d positive c b (tape ∘ bodyIndex)
      (fun stage => labels (.row stage)) (some (labels .clearTail)) stage
  | .clearTail => MachineDrain.drain (tape 0) (labels .clearTail) (some (labels .clearOld))
  | .clearOld => MachineDrain.drain (tape 1) (labels .clearOld) (some (labels .clearRelation))
  | .clearRelation => MachineDrain.drain (tape 2) (labels .clearRelation) (some (labels .clearNew))
  | .clearNew => MachineDrain.drain (tape 6) (labels .clearNew) exit

def inputRowBits (v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord j ++ encodeWords (relationWords relation)

def streamRowSteps (d c b v j : Nat) (relation : RelationTable) (output : List Bool) : Nat :=
  (v + 2) + (j + 2) + 1 + reindexSteps d c b v j relation output +
    (v + 2) + (j + 2) + ((encodeWords (relationWords relation)).length + 1) +
    (MachinePortReindex.value d c b j + 2)

def streamResultTapes (d c b v j : Nat) (relation : RelationTable)
    (tape : Fin 10 → K) (base : K → List Bool) (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) suffix) (tape 7)
    (base (tape 7) ++ reindexRowBits d c b v j relation)

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem streamRowTrace (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : StreamLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = streamInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (v j : Nat) (relation : RelationTable) (suffix : List Bool)
    (input : base (tape 9) = inputRowBits v j relation ++ suffix)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = []) (ambient : A) :
    (advance (TM2.step program))^[streamRowSteps d c b v j relation (base (tape 7))]
      (some ⟨some (labels .tailStart), streamClean d positive ambient, base⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamResultTapes d c b v j relation tape base suffix⟩ := by
  have hd (i k : Fin 10) (h : i ≠ k) : tape i ≠ tape k := fun x => h (distinct x)
  have hb6 : bodyIndex 6 = 6 := rfl
  have hb7 : bodyIndex 7 = 7 := rfl
  have h₀ := empty 0 (by decide) (by decide)
  have h₁ := empty 1 (by decide) (by decide)
  have h₂ := empty 2 (by decide) (by decide)
  have h₃ := empty 3 (by decide) (by decide)
  have h₄ := empty 4 (by decide) (by decide)
  have h₅ := empty 5 (by decide) (by decide)
  have h₆ := empty 6 (by decide) (by decide)
  have h₈ := empty 8 (by decide) (by decide)
  let relationBits := encodeWords (relationWords relation)
  let tailLoaded := Function.update (Function.update base (tape 9)
    (encodeWord j ++ (relationBits ++ suffix))) (tape 0) (encodeWord v)
  let reverseLoaded := Function.update (Function.update tailLoaded (tape 9)
    (relationBits ++ suffix)) (tape 1) (encodeWord j)
  let loaded := Function.update (Function.update reverseLoaded (tape 9) suffix) (tape 2) relationBits
  let rowed := reindexResultTapes d c b v j relation (tape ∘ bodyIndex) loaded
  let tailCleared := Function.update rowed (tape 0) []
  let oldCleared := Function.update tailCleared (tape 1) []
  let relationCleared := Function.update oldCleared (tape 2) []
  have tailRun : (advance (TM2.step program))^[v + 2]
      (some ⟨some (labels .tailStart), streamClean d positive ambient, base⟩) =
      some ⟨some (labels .reverseStart), streamClean d positive ambient, tailLoaded⟩ := by
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 0) (hd 9 0 (by decide))
      (labels .tailStart) (labels .tailRead) (some (labels .reverseStart)) program
      (atLabels .tailStart) (atLabels .tailRead) base v
      (encodeWord j ++ (relationBits ++ suffix))
      (by simpa only [inputRowBits, List.append_assoc] using input)
      ((ambient, MachineRegularOriginalRow.zeroBuffer),
        MachineFixedDivMod.residue d positive 0) none).evals_in_steps
    simp only [Hastad.SourceMachine.fieldInTime, Hastad.SourceMachine.fieldTapes,
      h₀, List.append_nil] at h
    convert h using 1 <;> rfl
  have reverseRun : (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .reverseStart), streamClean d positive ambient, tailLoaded⟩) =
      some ⟨some (labels .copyRelation), streamClean d positive ambient, reverseLoaded⟩ := by
    have hstart : tailLoaded (tape 1) = [] := by
      simp [tailLoaded, hd 1 0 (by decide), hd 1 9 (by decide), h₁]
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 1) (hd 9 1 (by decide))
      (labels .reverseStart) (labels .reverseRead) (some (labels .copyRelation)) program
      (atLabels .reverseStart) (atLabels .reverseRead) tailLoaded j (relationBits ++ suffix)
      (by simp [tailLoaded, hd 9 0 (by decide)])
      ((ambient, MachineRegularOriginalRow.zeroBuffer),
        MachineFixedDivMod.residue d positive 0) none).evals_in_steps
    simp only [Hastad.SourceMachine.fieldInTime, Hastad.SourceMachine.fieldTapes,
      hstart, List.append_nil] at h
    convert h using 1 <;> rfl
  have copyRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .copyRelation), streamClean d positive ambient, reverseLoaded⟩) =
      some ⟨some (labels (.row (.inl .copySeed))), streamClean d positive ambient, loaded⟩ := by
    have hempty : reverseLoaded (tape 2) = [] := by
      simp [reverseLoaded, tailLoaded, hd 2 1 (by decide), hd 2 9 (by decide),
        hd 2 0 (by decide), h₂]
    have h := streamRelationCopy_step d positive (tape 9) (tape 2) (hd 9 2 (by decide))
      (labels .copyRelation) (some (labels (.row (.inl .copySeed)))) program
      (atLabels .copyRelation) relation suffix reverseLoaded
      (by simp [reverseLoaded, relationBits, hd 9 1 (by decide)]) ambient
    simpa only [Function.iterate_one, advance_some, hempty, List.append_nil, loaded] using h
  have hs (i : Fin 10) (hi : i ≠ 0) (hi' : i ≠ 1) (hi'' : i ≠ 2) (hi''' : i ≠ 9) :
      loaded (tape i) = base (tape i) := by
    simp [loaded, reverseLoaded, tailLoaded, hd i 0 hi, hd i 1 hi',
      hd i 2 hi'', hd i 9 hi''']
  have loadedTail : loaded (tape 0) = encodeWord v := by
    simp [loaded, reverseLoaded, tailLoaded, hd 0 2 (by decide), hd 0 9 (by decide),
      hd 0 1 (by decide)]
  have loadedReverse : loaded (tape 1) = encodeWord j := by
    simp [loaded, reverseLoaded, hd 1 2 (by decide), hd 1 9 (by decide)]
  have loadedRelation : loaded (tape 2) = relationBits := by simp [loaded]
  have bodyRun := reindexRowTrace d positive c b (tape ∘ bodyIndex)
    (distinct.comp bodyIndex_injective) (fun stage => labels (.row stage))
    (some (labels .clearTail)) program (fun stage => atLabels (.row stage)) loaded v j relation
    loadedTail loadedReverse loadedRelation
    ((hs 3 (by decide) (by decide) (by decide) (by decide)).trans h₃)
    ((hs 4 (by decide) (by decide) (by decide) (by decide)).trans h₄)
    ((hs 5 (by decide) (by decide) (by decide) (by decide)).trans h₅)
    ((hs 6 (by decide) (by decide) (by decide) (by decide)).trans h₆)
    ((hs 8 (by decide) (by decide) (by decide) (by decide)).trans h₈)
    (ambient, MachineRegularOriginalRow.zeroBuffer)
  have hout : loaded ((tape ∘ bodyIndex) 7) = base (tape 7) :=
    hs 7 (by decide) (by decide) (by decide) (by decide)
  rw [hout] at bodyRun
  change (advance (TM2.step program))^[reindexSteps d c b v j relation (base (tape 7))]
    (some ⟨some (labels (.row (.inl .copySeed))), streamClean d positive ambient, loaded⟩) =
    some ⟨some (labels .clearTail), streamClean d positive ambient, rowed⟩ at bodyRun
  have rowedTail : rowed (tape 0) = encodeWord v := by
    simp only [rowed, reindexResultTapes, reindexMappedTapes, Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 0 7 (by decide)),
      Function.update_of_ne (hd 0 6 (by decide))] using loadedTail
  have rowedOld : tailCleared (tape 1) = encodeWord j := by
    simp only [tailCleared, rowed, reindexResultTapes, reindexMappedTapes,
      Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 1 0 (by decide)),
      Function.update_of_ne (hd 1 7 (by decide)), Function.update_of_ne (hd 1 6 (by decide))]
      using loadedReverse
  have rowedRelation : oldCleared (tape 2) = relationBits := by
    simp only [oldCleared, tailCleared, rowed, reindexResultTapes, reindexMappedTapes,
      Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 2 1 (by decide)),
      Function.update_of_ne (hd 2 0 (by decide)), Function.update_of_ne (hd 2 7 (by decide)),
      Function.update_of_ne (hd 2 6 (by decide))] using loadedRelation
  have rowedNew : relationCleared (tape 6) = encodeWord (MachinePortReindex.value d c b j) := by
    simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
      reindexMappedTapes, Function.comp_apply, bodyIndex, hd 6 2 (by decide),
      hd 6 1 (by decide), hd 6 0 (by decide), hd 6 7 (by decide)]
  have clearTail := (MachineDrain.drainInTime (tape 0) (labels .clearTail)
    (some (labels .clearOld)) program (atLabels .clearTail) rowed
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(rowed (tape 0)).length + 1]
    (some ⟨some (labels .clearTail), streamClean d positive ambient, rowed⟩) =
    some ⟨some (labels .clearOld), streamClean d positive ambient, tailCleared⟩ at clearTail
  rw [rowedTail, encodeWord_length] at clearTail
  have clearOld := (MachineDrain.drainInTime (tape 1) (labels .clearOld)
    (some (labels .clearRelation)) program (atLabels .clearOld) tailCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(tailCleared (tape 1)).length + 1]
    (some ⟨some (labels .clearOld), streamClean d positive ambient, tailCleared⟩) =
    some ⟨some (labels .clearRelation), streamClean d positive ambient, oldCleared⟩ at clearOld
  rw [rowedOld, encodeWord_length] at clearOld
  have clearRelation := (MachineDrain.drainInTime (tape 2) (labels .clearRelation)
    (some (labels .clearNew)) program (atLabels .clearRelation) oldCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(oldCleared (tape 2)).length + 1]
    (some ⟨some (labels .clearRelation), streamClean d positive ambient, oldCleared⟩) =
    some ⟨some (labels .clearNew), streamClean d positive ambient, relationCleared⟩ at clearRelation
  rw [rowedRelation] at clearRelation
  have clearNew := (MachineDrain.drainInTime (tape 6) (labels .clearNew)
    exit program (atLabels .clearNew) relationCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(relationCleared (tape 6)).length + 1]
    (some ⟨some (labels .clearNew), streamClean d positive ambient, relationCleared⟩) =
    some ⟨exit, streamClean d positive ambient,
      Function.update relationCleared (tape 6) []⟩ at clearNew
  rw [rowedNew, encodeWord_length] at clearNew
  have finalFrame : Function.update relationCleared (tape 6) [] =
      streamResultTapes d c b v j relation tape base suffix := by
    funext k
    by_cases h6 : k = tape 6
    · subst k
      simp [streamResultTapes, hd 6 7 (by decide), hd 6 9 (by decide), h₆]
    · by_cases h2 : k = tape 2
      · subst k
        simp [relationCleared, streamResultTapes, hd 2 6 (by decide),
          hd 2 7 (by decide), hd 2 9 (by decide), h₂]
      · by_cases h1 : k = tape 1
        · subst k
          simp [relationCleared, oldCleared, streamResultTapes,
            hd 1 6 (by decide), hd 1 2 (by decide), hd 1 7 (by decide),
            hd 1 9 (by decide), h₁]
        · by_cases h0 : k = tape 0
          · subst k
            simp [relationCleared, oldCleared, tailCleared, streamResultTapes,
              hd 0 6 (by decide), hd 0 2 (by decide), hd 0 1 (by decide),
              hd 0 7 (by decide), hd 0 9 (by decide), h₀]
          · by_cases h7 : k = tape 7
            · subst k
              simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                reindexMappedTapes, Function.comp_apply, bodyIndex, streamResultTapes,
                loaded, reverseLoaded, tailLoaded, hd 7 6 (by decide), hd 7 2 (by decide),
                hd 7 1 (by decide), hd 7 0 (by decide), hd 7 9 (by decide)]
            · by_cases h9 : k = tape 9
              · subst k
                simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                  reindexMappedTapes, Function.comp_apply, bodyIndex, loaded, reverseLoaded,
                  tailLoaded, streamResultTapes, hd 9 6 (by decide), hd 9 2 (by decide),
                  hd 9 1 (by decide), hd 9 0 (by decide), hd 9 7 (by decide)]
              · simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                  reindexMappedTapes, Function.comp_apply, bodyIndex, loaded, reverseLoaded,
                  tailLoaded, streamResultTapes, h6, h2, h1, h0, h7, h9]
  rw [finalFrame] at clearNew
  exact joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace tailRun reverseRun) copyRun) bodyRun) clearTail) clearOld) clearRelation) clearNew

abbrev VertexLabel (d : Nat) := Fin (d + 1) × Option (StreamLabel d)

def vertexInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (labels : VertexLabel d → Λ) (exit : Option Λ) :
    VertexLabel d → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d)
  | (i, none) => if i.val < d then .goto fun _ => labels (i, some .tailStart)
      else MachinePortReindex.exitAt exit
  | (i, some stage) => if h : i.val < d then
      streamInstruction d positive c b tape (fun stage => labels (i, some stage))
        (some (labels (⟨i.val + 1, by omega⟩, none))) stage
      else MachinePortReindex.exitAt exit

def recordsInput {n m : Nat} (rows : List (DartRow n m)) : List Bool :=
  rows.flatMap (fun r => inputRowBits r.tail.val r.reverseIndex.val r.relation)

def recordsOutput {n m : Nat} (d c b : Nat) (rows : List (DartRow n m)) : List Bool :=
  rows.flatMap (fun r => reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation)

def streamFrame {n m : Nat} (tape : Fin 10 → K) (base : K → List Bool)
    (rows : List (DartRow n m)) (output : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) (recordsInput rows ++ base (tape 9)))
    (tape 7) output

def vertexSteps {n m : Nat} (d c b : Nat) : List (DartRow n m) → List Bool → Nat
  | [], _ => 1
  | r :: rows, output => 1 + streamRowSteps d c b r.tail.val r.reverseIndex.val r.relation output +
      vertexSteps d c b rows
        (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation)

theorem recordsInput_eq_codec {n m : Nat} (rows : List (DartRow n m)) :
    recordsInput rows = encodeWords (rows.flatMap rowWords) := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
      simp only [recordsInput, List.flatMap_cons, encodeWords_append,
        MachineTableRows.rowBits_eq, inputRowBits] at ih ⊢
      rw [ih]

private theorem streamFrame_afterRow {n m : Nat} (d c b : Nat) (r : DartRow n m)
    (tape : Fin 10 → K) (distinct : Function.Injective tape) (base : K → List Bool)
    (rows : List (DartRow n m)) (output : List Bool) :
    streamResultTapes d c b r.tail.val r.reverseIndex.val r.relation tape
      (streamFrame tape base (r :: rows) output) (recordsInput rows ++ base (tape 9)) =
      streamFrame tape base rows
        (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) := by
  have h79 : tape 7 ≠ tape 9 := fun h => (by decide : (7 : Fin 10) ≠ 9) (distinct h)
  funext k
  by_cases h7 : k = tape 7
  · subst k
    simp [streamResultTapes, streamFrame]
  · by_cases h9 : k = tape 9
    · subst k
      simp [streamResultTapes, streamFrame, Ne.symm h79]
    · simp [streamResultTapes, streamFrame, h7, h9]

theorem vertexSuffixTrace {n m : Nat} (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (labels : VertexLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (rows : Fin d → DartRow n m)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = []) (ambient : A)
    (remaining : Nat) (i : Fin (d + 1)) (count : i.val + remaining = d) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d c b ((List.ofFn rows).drop i.val) output]
      (some ⟨some (labels (i, none)), streamClean d positive ambient,
        streamFrame tape base ((List.ofFn rows).drop i.val) output⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamFrame (n := n) (m := m) tape base []
          (output ++ recordsOutput d c b ((List.ofFn rows).drop i.val))⟩ := by
  have hd (a k : Fin 10) (h : a ≠ k) : tape a ≠ tape k := fun x => h (distinct x)
  induction remaining generalizing i output with
  | zero =>
      have hi : i.val = d := by omega
      have hdrop : (List.ofFn rows).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [List.length_ofFn, hi, le_refl]
      rw [hdrop]
      simp only [vertexSteps, recordsOutput, List.flatMap_nil, List.append_nil]
      change some (TM2.stepAux (program (labels (i, none))) _ _) = _
      rw [atLabels]
      cases exit <;> simp [vertexInstruction, hi, MachinePortReindex.exitAt, TM2.stepAux]
  | succ remaining ih =>
      have hi : i.val < d := by omega
      let port : Fin d := ⟨i.val, hi⟩
      let next : Fin (d + 1) := ⟨i.val + 1, by omega⟩
      let rest := (List.ofFn rows).drop (i.val + 1)
      have split : (List.ofFn rows).drop i.val = rows port :: rest := by
        have h := List.getElem_cons_drop (as := List.ofFn rows)
          (i := i.val) (by simpa only [List.length_ofFn] using hi)
        simpa only [List.getElem_ofFn, port, rest] using h.symm
      let initial := streamFrame tape base (rows port :: rest) output
      have boundary : (advance (TM2.step program))^[1]
          (some ⟨some (labels (i, none)), streamClean d positive ambient, initial⟩) =
          some ⟨some (labels (i, some .tailStart)), streamClean d positive ambient, initial⟩ := by
        change some (TM2.stepAux (program (labels (i, none))) _ _) = _
        rw [atLabels]
        simp [vertexInstruction, hi, TM2.stepAux]
      have body := streamRowTrace d positive c b tape distinct
        (fun stage => labels (i, some stage)) (some (labels (next, none))) program
        (by
          intro stage
          simpa only [vertexInstruction, hi, dite_true, next] using (atLabels (i, some stage)))
        initial (rows port).tail.val (rows port).reverseIndex.val (rows port).relation
        (recordsInput rest ++ base (tape 9))
        (by simp [initial, streamFrame, hd 9 7 (by decide), recordsInput, List.append_assoc])
        (by
          intro k hk7 hk9
          simp [initial, streamFrame, hd k 7 hk7, hd k 9 hk9, empty k hk7 hk9]) ambient
      have initialOutput : initial (tape 7) = output := by simp [initial, streamFrame]
      rw [initialOutput] at body
      change (advance (TM2.step program))^[streamRowSteps d c b
        (rows port).tail.val (rows port).reverseIndex.val (rows port).relation output]
        (some ⟨some (labels (i, some .tailStart)), streamClean d positive ambient, initial⟩) =
        some ⟨some (labels (next, none)), streamClean d positive ambient,
          streamResultTapes d c b (rows port).tail.val (rows port).reverseIndex.val
            (rows port).relation tape initial (recordsInput rest ++ base (tape 9))⟩ at body
      rw [show streamResultTapes d c b (rows port).tail.val (rows port).reverseIndex.val
        (rows port).relation tape initial (recordsInput rest ++ base (tape 9)) =
        streamFrame tape base rest
          (output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation) from
          streamFrame_afterRow d c b (rows port) tape distinct base rest output] at body
      have nextCount : next.val + remaining = d := by dsimp [next]; omega
      have tail := ih next nextCount
        (output ++ reindexRowBits d c b (rows port).tail.val
          (rows port).reverseIndex.val (rows port).relation)
      change (advance (TM2.step program))^[vertexSteps d c b rest
        (output ++ reindexRowBits d c b (rows port).tail.val
          (rows port).reverseIndex.val (rows port).relation)]
        (some ⟨some (labels (next, none)), streamClean d positive ambient,
          streamFrame tape base rest (output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation)⟩) =
        some ⟨exit, streamClean d positive ambient,
          streamFrame (n := n) (m := m) tape base [] ((output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation) ++ recordsOutput d c b rest)⟩ at tail
      rw [split]
      have all := joinTrace (joinTrace boundary body) tail
      simpa only [vertexSteps, initial, recordsOutput, List.flatMap_cons, List.append_assoc] using all

theorem vertexTrace {n m : Nat} (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (labels : VertexLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (rows : Fin d → DartRow n m)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d c b (List.ofFn rows) output]
      (some ⟨some (labels (0, none)), streamClean d positive ambient,
        streamFrame tape base (List.ofFn rows) output⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamFrame (n := n) (m := m) tape base [] (output ++ recordsOutput d c b (List.ofFn rows))⟩ := by
  simpa only [Fin.val_zero, List.drop_zero] using vertexSuffixTrace d positive c b tape distinct
    labels exit program atLabels base rows empty ambient d 0 (by simp) output

private theorem encodeWords_flatMap {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem recordsOutput_lazy {n d : Nat} (table : PCP.PortTables.Table n d) (v : Fin n) :
    recordsOutput d (2 * d) d (List.ofFn (PCP.PreprocessingLazyWords.row table v)) =
      encodeWords ((List.ofFn (moveRow table v)).flatMap rowWords) := by
  rw [encodeWords_flatMap]
  simp only [recordsOutput, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  change reindexRowBits d (2 * d) d v.val
      (PCP.PreprocessingLazyWords.row table v p).reverseIndex.val
      (PCP.PreprocessingLazyWords.row table v p).relation =
    encodeWords (rowWords (moveRow table v p))
  have h := rowBits_eq_moveRow table v p
  simpa only [rowBits, reindexRowBits, MachinePortReindex.lazy_value, reverseMap] using h

def valueBound (c b m : Nat) : Nat := c * m + m + b
def rowSizeBound (c b n m : Nat) : Nat := n + valueBound c b m + 8194
def rowCostBound (c b n m : Nat) : Nat :=
  2 * n + 8 * m + valueBound c b m + 4 * rowSizeBound c b n m + 8224

theorem reindexValue_le {n m : Nat} (d c b : Nat) (r : DartRow n m) :
    MachinePortReindex.value d c b r.reverseIndex.val ≤ valueBound c b m := by
  have hj := r.reverseIndex.isLt.le
  have hdiv := (Nat.div_le_self r.reverseIndex.val d).trans hj
  have hmod := (Nat.mod_le r.reverseIndex.val d).trans hj
  have hmul := Nat.mul_le_mul_left c hdiv
  unfold MachinePortReindex.value valueBound
  omega

theorem reindexRowBits_length_le {n m : Nat} (d c b : Nat) (r : DartRow n m) :
    (reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation).length ≤
      rowSizeBound c b n m := by
  have htail := r.tail.isLt.le
  have hvalue := reindexValue_le d c b r
  have hrelation := relationBits_length_le r.relation
  simp only [reindexRowBits, List.length_append, encodeWord_length]
  unfold rowSizeBound
  omega

theorem streamRowSteps_le {n m : Nat} (d c b : Nat) (r : DartRow n m) (output : List Bool) :
    streamRowSteps d c b r.tail.val r.reverseIndex.val r.relation output ≤
      rowCostBound c b n m + 2 * output.length := by
  have htail := r.tail.isLt.le
  have hj := r.reverseIndex.isLt.le
  have hdiv := (Nat.div_le_self r.reverseIndex.val d).trans hj
  have hvalue := reindexValue_le d c b r
  have hrelation := relationBits_length_le r.relation
  have hsize := reindexRowBits_length_le d c b r
  unfold streamRowSteps reindexSteps MachinePortReindex.steps rowCostBound
  omega

private theorem vertexSteps_le_capacity {n m : Nat} (d c b capacity : Nat)
    (rows : List (DartRow n m)) (output : List Bool)
    (room : output.length + rows.length * rowSizeBound c b n m ≤ capacity) :
    vertexSteps d c b rows output ≤
      rows.length * (rowCostBound c b n m + 2 * capacity + 1) + 1 := by
  induction rows generalizing output with
  | nil => simp [vertexSteps]
  | cons r rows ih =>
      have hsize := reindexRowBits_length_le d c b r
      have hcost := streamRowSteps_le d c b r output
      have hout : output.length ≤ capacity := by omega
      have hroom : (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation).length +
          rows.length * rowSizeBound c b n m ≤ capacity := by
        rw [List.length_append]
        simp only [List.length_cons, Nat.succ_mul] at room
        omega
      have htail := ih
        (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) hroom
      change 1 + streamRowSteps d c b r.tail.val r.reverseIndex.val r.relation output +
        vertexSteps d c b rows
          (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) ≤
        (rows.length + 1) * (rowCostBound c b n m + 2 * capacity + 1) + 1
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem vertexSteps_le {n m : Nat} (d c b : Nat) (rows : List (DartRow n m))
    (output : List Bool) :
    vertexSteps d c b rows output ≤ rows.length * (rowCostBound c b n m +
      2 * (output.length + rows.length * rowSizeBound c b n m) + 1) + 1 :=
  vertexSteps_le_capacity d c b _ rows output (Nat.le_refl _)

def vertexInTime {n m : Nat} (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (labels : VertexLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (rows : Fin d → DartRow n m)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (output : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (0, none)), streamClean d positive ambient,
        streamFrame tape base (List.ofFn rows) output⟩
      (some ⟨exit, streamClean d positive ambient,
        streamFrame (n := n) (m := m) tape base []
          (output ++ recordsOutput d c b (List.ofFn rows))⟩)
      (d * (rowCostBound c b n m + 2 * (output.length + d * rowSizeBound c b n m) + 1) + 1) where
  steps := vertexSteps d c b (List.ofFn rows) output
  evals_in_steps := vertexTrace d positive c b tape distinct labels exit program atLabels
    base rows empty ambient output
  steps_le_m := by
    simpa only [List.length_ofFn] using vertexSteps_le d c b (List.ofFn rows) output

def vertexMachine (d : Nat) (positive : 0 < d) (c b : Nat) : FinTM2 where
  K := Fin 10
  k₀ := 9
  k₁ := 7
  Γ _ := Bool
  Λ := VertexLabel d
  main := (0, none)
  σ := StreamState Unit d
  initialState := streamClean d positive ()
  m := vertexInstruction d positive c b id id none

end BinPackingGames.Foundations.Complexity.MachineLazyRows

end OAI
