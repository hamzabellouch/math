import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.PreprocessingRegularTables
import OAI.Combinatorics.IndependentSets.Machines.MachineStateEquiv
import OAI.Combinatorics.IndependentSets.Machines.Block
import OAI.Combinatorics.IndependentSets.Machines.MachineAffineLookup
import OAI.Combinatorics.IndependentSets.Machines.MachineTableRows

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularOriginalRow

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

end IndependentSetsGames.Foundations.Complexity.MachineRegularOriginalRow

end OAI
