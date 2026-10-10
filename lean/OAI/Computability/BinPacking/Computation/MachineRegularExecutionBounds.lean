import Mathlib.Tactic.FinCases
import OAI.Computability.BinPacking.Computation.MachineLazyRows
import OAI.Computability.BinPacking.Computation.MachinePaddedExpanderFamily
import OAI.Computability.BinPacking.Computation.MachineRegularInternalRow
import OAI.Computability.BinPacking.PCP.PreprocessingRegularBounds

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularMetadata

open Turing MachineComposition
open BinPackingGames.Foundations.PCP

inductive Extra
  | padding | level
  deriving DecidableEq

protected abbrev Extra.enumList : List Extra := [.padding, .level]

protected theorem Extra.enumList_getElem?_ctorIdx_eq (x : Extra) :
    Extra.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Extra.enumList_nodup : Extra.enumList.Nodup := by decide

instance : Fintype Extra where
  elems := ⟨Extra.enumList, Extra.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 27 ⊕ Extra
abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

inductive Label
  | owner (l : MachineAffineLookup.Label)
  | ownerClearQuery | ownerClearWork
  | copyXFirst | copyXSecond | copyOwnerFirst | copyOwnerSecond | rankInit
  | rank (l : MachineCloudRank.RankLabel)
  | rankClearQuery | rankClearWork | rankClearFuel
  | prefixCode (l : MachineCloudPrefix.Label)
  | prefixClearQuery | prefixClearFuel
  | cloud (l : MachineCloudPadding.Label)
  deriving DecidableEq, Fintype

def ownerTapes : Fin 5 → Tape := ![.inl 0, .inl 9, .inl 10, .inl 2, .inl 11]

def rankTape : MachineCloudCount.Tape → Tape
  | .original => .inl 0
  | .work => .inl 10
  | .target => .inl 9
  | .scratch => .inl 11
  | .count => .inl 3
  | .spare => .inl 12

def prefixTape : MachineCloudPrefix.Tape → Tape
  | .inner .table => .inl 0
  | .inner .query => .inl 9
  | .inner .count => .inl 10
  | .inner .work => .inl 11
  | .inner .scratch => .inl 12
  | .inner .spare => .inl 13
  | .inner .power => .inl 14
  | .inner .level => .inl 15
  | .inner .fuel => .inl 16
  | .inner .product => .inl 17
  | .bound => .inl 2
  | .remaining => .inl 18
  | .total => .inl 5

def cloudTape : MachineCloudPadding.Tape → Tape
  | .table => .inl 0
  | .query => .inl 2
  | .count => .inl 4
  | .work => .inl 9
  | .scratch => .inl 10
  | .spare => .inl 11
  | .power => .inr .padding
  | .level => .inr .level
  | .fuel => .inl 12
  | .product => .inl 13

variable {σ : Type}

def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .owner l => MachineAffineLookup.instruction (.inl 1) ownerTapes 4098 2
      Label.owner (some .ownerClearQuery) l
  | .ownerClearQuery => MachineDrain.drain (.inl 9) .ownerClearQuery (some .ownerClearWork)
  | .ownerClearWork => MachineDrain.drain (.inl 10) .ownerClearWork (some .copyXFirst)
  | .copyXFirst => Reduction.MachineTransfer.loopAt (.inl 1) (.inl 10) id false
      .copyXFirst (some .copyXSecond)
  | .copyXSecond => MachineCopy.forkLoop (.inl 10) (.inl 1) (.inl 9) false
      .copyXSecond (some .copyOwnerFirst)
  | .copyOwnerFirst => Reduction.MachineTransfer.loopAt (.inl 2) (.inl 10) id false
      .copyOwnerFirst (some .copyOwnerSecond)
  | .copyOwnerSecond => MachineCopy.forkLoop (.inl 10) (.inl 2) (.inl 9) false
      .copyOwnerSecond (some .rankInit)
  | .rankInit => .push (.inl 3) (fun _ => false) (.goto fun _ => .rank .queryFirst)
  | .rank l => MachineCloudPadding.Placement.statement rankTape Label.rank
      (some .rankClearQuery) (MachineCloudRank.rankProgram l)
  | .rankClearQuery => MachineDrain.drain (.inl 9) .rankClearQuery (some .rankClearWork)
  | .rankClearWork => MachineDrain.drain (.inl 10) .rankClearWork (some .rankClearFuel)
  | .rankClearFuel => MachineDrain.drain (.inl 12) .rankClearFuel (some (.prefixCode .init))
  | .prefixCode l => MachineCloudPadding.Placement.statement prefixTape Label.prefixCode
      (some .prefixClearQuery) (MachineCloudPrefix.program l)
  | .prefixClearQuery => MachineDrain.drain (.inl 9) .prefixClearQuery (some .prefixClearFuel)
  | .prefixClearFuel => MachineDrain.drain (.inl 18) .prefixClearFuel (some (.cloud .init))
  | .cloud l => MachineCloudPadding.Placement.statement cloudTape Label.cloud none
      (MachineCloudPadding.program l)

def rankView : Tape → Option MachineCloudCount.Tape
  | .inl i => match i.val with
    | 0 => some .original
    | 10 => some .work
    | 9 => some .target
    | 11 => some .scratch
    | 3 => some .count
    | 12 => some .spare
    | _ => none
  | .inr _ => none

def prefixView : Tape → Option MachineCloudPrefix.Tape
  | .inl i => match i.val with
    | 0 => some (.inner .table)
    | 9 => some (.inner .query)
    | 10 => some (.inner .count)
    | 11 => some (.inner .work)
    | 12 => some (.inner .scratch)
    | 13 => some (.inner .spare)
    | 14 => some (.inner .power)
    | 15 => some (.inner .level)
    | 16 => some (.inner .fuel)
    | 17 => some (.inner .product)
    | 2 => some .bound
    | 18 => some .remaining
    | 5 => some .total
    | _ => none
  | .inr _ => none

def cloudView : Tape → Option MachineCloudPadding.Tape
  | .inl i => match i.val with
    | 0 => some .table
    | 2 => some .query
    | 4 => some .count
    | 9 => some .work
    | 10 => some .scratch
    | 11 => some .spare
    | 12 => some .fuel
    | 13 => some .product
    | _ => none
  | .inr .padding => some .power
  | .inr .level => some .level

theorem rankView_left (k : MachineCloudCount.Tape) : rankView (rankTape k) = some k := by
  cases k <;> rfl
theorem rankView_right (j : Tape) (k : MachineCloudCount.Tape)
    (h : rankView j = some k) : rankTape k = j := by
  cases j with
  | inl j => fin_cases j <;> simp_all [rankView, rankTape] <;> subst k <;> rfl
  | inr j => simp_all [rankView]

theorem prefixView_left (k : MachineCloudPrefix.Tape) : prefixView (prefixTape k) = some k := by
  cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
theorem prefixView_right (j : Tape) (k : MachineCloudPrefix.Tape)
    (h : prefixView j = some k) : prefixTape k = j := by
  cases j with
  | inl j => fin_cases j <;> simp_all [prefixView, prefixTape] <;> subst k <;> rfl
  | inr j => simp_all [prefixView]

theorem cloudView_left (k : MachineCloudPadding.Tape) : cloudView (cloudTape k) = some k := by
  cases k <;> rfl
theorem cloudView_right (j : Tape) (k : MachineCloudPadding.Tape)
    (h : cloudView j = some k) : cloudTape k = j := by
  cases j with
  | inl j => fin_cases j <;> simp_all [cloudView, cloudTape] <;> subst k <;> rfl
  | inr j => cases j <;> simp_all [cloudView, cloudTape] <;> subst k <;> rfl

structure Data where
  table : List Bool
  globalIndex : List Bool
  owner : List Bool
  localRank : List Bool
  count : List Bool
  offset : List Bool
  darts : List Bool
  rotor : List Bool
  output : List Bool
  padding : List Bool
  level : List Bool

def frame (data : Data) : Tape → List Bool
  | .inl i => match i.val with
    | 0 => data.table
    | 1 => data.globalIndex
    | 2 => data.owner
    | 3 => data.localRank
    | 4 => data.count
    | 5 => data.offset
    | 6 => data.darts
    | 7 => data.rotor
    | 8 => data.output
    | _ => []
  | .inr .padding => data.padding
  | .inr .level => data.level

@[simp] theorem frame_index (data : Data) :
    frame data (.inl 1) = data.globalIndex := rfl

@[simp] theorem frame_query_empty (data : Data) :
    frame data (.inl 9) = [] := rfl

def cfg (label : Option Label) (data : Data) (ambient : σ) (register : Option Bool) :
    TM2.Cfg Alphabet Label (State σ) :=
  ⟨label, ((ambient, false), register), frame data⟩

def cloudData (t : GraphTables.Table) (v : Fin t.vertices) (data : Data) : Data :=
  { data with
    count := encodeWord (PreprocessingCloudIndex.cloudSize t v)
    padding := encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v))
    level := encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)) }

theorem cloudTrace (t : GraphTables.Table) (v : Fin t.vertices) (data : Data)
    (htable : data.table = GraphTables.tableBits t) (howner : data.owner = encodeWord v.val)
    (hcount : data.count = []) (hpadding : data.padding = []) (hlevel : data.level = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineCloudPadding.totalTime t v]
      (some (cfg (some (.cloud .init)) data ambient register)) =
      some (cfg none (cloudData t v data) ambient none) := by
  have raw := MachineCloudPadding.cloudPaddingTrace t v [] ambient register
  simp only [List.append_nil] at raw
  have placed := MachineCloudPadding.Placement.trace cloudTape cloudView cloudView_left cloudView_right
    Label.cloud none (frame data) MachineCloudPadding.program program (fun _ => rfl)
    (MachineCloudPadding.totalTime t v) _ _ raw
  have hstart : MachineCloudPadding.Placement.tapes cloudView
      (MachineCloudPadding.memory (GraphTables.tableBits t) (encodeWord v.val)
        [] [] [] [] [] [] [] []) (frame data) = frame data := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp_all [MachineCloudPadding.Placement.tapes, cloudView, frame, MachineCloudPadding.memory]
    | inr j => cases j <;>
        simp_all [MachineCloudPadding.Placement.tapes, cloudView, frame, MachineCloudPadding.memory]
  have hfinish : MachineCloudPadding.Placement.tapes cloudView
      (MachineCloudPadding.memory (GraphTables.tableBits t) (encodeWord v.val)
        (encodeWord (PreprocessingCloudIndex.cloudSize t v)) [] [] []
        (encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v)))
        (encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v))) [] [])
      (frame data) = frame (cloudData t v data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp_all [MachineCloudPadding.Placement.tapes, cloudView, frame, cloudData, MachineCloudPadding.memory]
    | inr j => cases j <;>
        simp_all [MachineCloudPadding.Placement.tapes, cloudView, frame, cloudData, MachineCloudPadding.memory]
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    hstart, hfinish, cfg] using placed

private theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

private theorem drainAt (source : Tape) (again : Label) (exit : Option Label)
    (code : program (σ := σ) again = MachineDrain.drain source again exit)
    (base : Tape → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[(base source).length + 1]
      (some ⟨some again, ((ambient, false), register), base⟩) =
      some ⟨exit, ((ambient, false), none), Function.update base source []⟩ := by
  simpa only [Function.update_eq_self] using
    MachineDrain.drainTrace source again exit program code base (base source)
      (ambient, false) register

def prefixData (t : GraphTables.Table) (v : Fin t.vertices) (data : Data) : Data :=
  { data with offset := encodeWord (PreprocessingPaddingOffsets.offset
      (PreprocessingRegularTables.padding t) v.val) }

def prefixSteps (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  MachineCloudPrefix.totalTime t v.val [] + (v.val + 2) + 2

theorem prefixTrace (t : GraphTables.Table) (v : Fin t.vertices) (data : Data)
    (htable : data.table = GraphTables.tableBits t) (howner : data.owner = encodeWord v.val)
    (hoffset : data.offset = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixSteps t v]
      (some (cfg (some (.prefixCode .init)) data ambient register)) =
      some (cfg (some (.cloud .init)) (prefixData t v data) ambient none) := by
  have raw := MachineCloudPrefix.prefixTrace t v.val v.isLt.le [] ambient register
  simp only [List.append_nil] at raw
  let mid := MachineCloudPadding.Placement.tapes prefixView
    (MachineCloudPrefix.frame (GraphTables.tableBits t) (encodeWord v.val) [] [] []
      (encodeWord v.val) (encodeWord 0)
      (encodeWord (PreprocessingPaddingOffsets.offset
        (PreprocessingRegularTables.padding t) v.val))) (frame data)
  have placed := MachineCloudPadding.Placement.trace prefixTape prefixView prefixView_left
    prefixView_right Label.prefixCode (some .prefixClearQuery) (frame data)
    MachineCloudPrefix.program program (fun _ => rfl)
    (MachineCloudPrefix.totalTime t v.val []) _ _ raw
  have hstart : MachineCloudPadding.Placement.tapes prefixView
      (MachineCloudPrefix.frame (GraphTables.tableBits t) [] [] [] [] (encodeWord v.val) [] [])
      (frame data) = frame data := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [htable, howner, hoffset, MachineCloudPadding.Placement.tapes, prefixView, frame,
          MachineCloudPrefix.frame, MachineCloudPrefix.memory, MachineCloudPadding.memory]
    | inr j => cases j <;> rfl
  have phase : (advance (TM2.step program))^[MachineCloudPrefix.totalTime t v.val []]
      (some (cfg (some (.prefixCode .init)) data ambient register)) =
      some ⟨some .prefixClearQuery, ((ambient, false), none), mid⟩ := by
    simpa only [MachineCloudPadding.Placement.configuration,
      MachineCloudPadding.Placement.label, hstart, cfg, mid] using placed
  have first := drainAt (.inl 9) .prefixClearQuery (some .prefixClearFuel) rfl mid ambient none
  have second := drainAt (.inl 18) .prefixClearFuel (some (.cloud .init)) rfl
    (Function.update mid (.inl 9) []) ambient none
  have hquery : (mid (.inl 9)).length + 1 = v.val + 2 := by
    simp [mid, MachineCloudPadding.Placement.tapes, prefixView, MachineCloudPrefix.frame, MachineCloudPrefix.memory,
      MachineCloudPadding.memory, encodeWord_length]
  have hfuel : ((Function.update mid (.inl 9) []) (.inl 18)).length + 1 = 2 := by
    simp [mid, MachineCloudPadding.Placement.tapes, prefixView, MachineCloudPrefix.frame, MachineCloudPrefix.memory,
      encodeWord_length]
  have hfinish : Function.update (Function.update mid (.inl 9) []) (.inl 18) [] =
      frame (prefixData t v data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [htable, howner, mid, MachineCloudPadding.Placement.tapes, prefixView, frame, prefixData,
          MachineCloudPrefix.frame, MachineCloudPrefix.memory, MachineCloudPadding.memory]
    | inr j => cases j <;> rfl
  rw [hquery] at first
  rw [hfuel, hfinish] at second
  exact join_trace (join_trace phase first) second

theorem selected_owner (t : GraphTables.Table) (e : Fin t.darts) :
    (GraphTables.tableWords t)[4098 * e.val + 2]? = some t.rows[e].tail.val := by
  have h := congrArg (fun words : List Nat => words[0]?)
    (MachineRegularOriginalRow.tableWords_drop_row t e)
  simp only [List.getElem?_drop, Nat.add_zero] at h
  rw [show 2 + 4098 * e.val = 4098 * e.val + 2 by omega] at h
  simpa [GraphTables.rowWords] using h

def ownerData (t : GraphTables.Table) (e : Fin t.darts) (data : Data) : Data :=
  { data with owner := encodeWord t.rows[e].tail.val }

def ownerRemainder (t : GraphTables.Table) (e : Fin t.darts) : List Bool :=
  encodeWords ((GraphTables.tableWords t).drop (4098 * e.val + 2 + 1))

def ownerSteps (t : GraphTables.Table) (e : Fin t.darts) : Nat :=
  MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 2 + 2 +
    ((ownerRemainder t e).length + 1)

theorem ownerTrace (t : GraphTables.Table) (e : Fin t.darts) (data : Data)
    (htable : data.table = GraphTables.tableBits t)
    (hindex : data.globalIndex = encodeWord e.val) (howner : data.owner = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[ownerSteps t e]
      (some (cfg (some (.owner .seed)) data ambient register)) =
      some (cfg (some .copyXFirst) (ownerData t e data) ambient none) := by
  have distinct : Function.Injective ownerTapes := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [ownerTapes]
  have outside : ∀ i, (.inl 1 : Tape) ≠ ownerTapes i := by
    intro i
    fin_cases i <;> decide
  let mid := MachineAffineLookup.finalTapes ownerTapes (frame data)
    (GraphTables.tableWords t) (4098 * e.val + 2) t.rows[e].tail.val
  have phase : (advance (TM2.step program))^[
      MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 2]
      (some (cfg (some (.owner .seed)) data ambient register)) =
      some ⟨some .ownerClearQuery, ((ambient, false), none), mid⟩ := by
    exact MachineAffineLookup.affineLookupTrace (.inl 1) ownerTapes distinct outside 4098 2
      Label.owner (some .ownerClearQuery) program (fun _ => rfl) (frame data)
      (GraphTables.tableWords t) htable rfl e.val []
      (by change data.globalIndex = encodeWord e.val ++ [];
          simpa only [List.append_nil] using hindex)
      t.rows[e].tail.val (selected_owner t e) (ambient, false) register
  have first := drainAt (.inl 9) .ownerClearQuery (some .ownerClearWork) rfl mid ambient none
  have second := drainAt (.inl 10) .ownerClearWork (some .copyXFirst) rfl
    (Function.update mid (.inl 9) []) ambient none
  have hquery : (mid (.inl 9)).length + 1 = 2 := by
    simp [mid, MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
      MachineLookup.tapes, ownerTapes, frame, encodeWord_length]
  have hwork : (Function.update mid (.inl 9) []) (.inl 10) = ownerRemainder t e := by
    simp [mid, MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
      MachineLookup.tapes, ownerTapes, frame, ownerRemainder]
  have hfinish : Function.update (Function.update mid (.inl 9) []) (.inl 10) [] =
      frame (ownerData t e data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [howner, mid, MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
          MachineLookup.tapes, ownerTapes, frame, ownerData]
    | inr j => cases j <;> rfl
  rw [hquery] at first
  rw [hwork, hfinish] at second
  exact join_trace (join_trace phase first) second

def rankQuery (v x : Nat) : List Bool := MachineCloudRank.queryWord v x []

def queryFrame (data : Data) (v x : Nat) : Tape → List Bool :=
  Function.update (Function.update (frame data) (.inl 9) (rankQuery v x))
    (.inl 3) (encodeWord 0)

def querySteps (v x : Nat) : Nat := 2 * (x + 2) + 2 * (v + 2) + 1

theorem queryTrace (data : Data) (v x : Nat)
    (howner : data.owner = encodeWord v) (hindex : data.globalIndex = encodeWord x)
    (hrank : data.localRank = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[querySteps v x]
      (some (cfg (some .copyXFirst) data ambient register)) =
      some ⟨some (.rank .queryFirst), ((ambient, false), none), queryFrame data v x⟩ := by
  let first := Function.update (frame data) (.inl 9) data.globalIndex
  let second := Function.update first (.inl 9) (data.owner ++ data.globalIndex)
  have copyX := MachineCopy.copyTrace (.inl 1 : Tape) (.inl 9) (.inl 10)
    (by decide) (by decide) (by decide) false Label.copyXFirst Label.copyXSecond
    (some .copyOwnerFirst) program rfl rfl (frame data) rfl (ambient, false) register
  have copyOwner := MachineCopy.copyTrace (.inl 2 : Tape) (.inl 9) (.inl 10)
    (by decide) (by decide) (by decide) false Label.copyOwnerFirst Label.copyOwnerSecond
    (some .rankInit) program rfl rfl first (by simp [first, frame]) (ambient, false) none
  have firstRun : (advance (TM2.step program))^[2 * (x + 2)]
      (some (cfg (some .copyXFirst) data ambient register)) =
      some ⟨some .copyOwnerFirst, ((ambient, false), none), first⟩ := by
    simpa only [frame_index, frame_query_empty, hindex, encodeWord_length,
      List.append_nil, cfg, first] using copyX
  have secondRun : (advance (TM2.step program))^[2 * (v + 2)]
      (some ⟨some .copyOwnerFirst, ((ambient, false), none), first⟩) =
      some ⟨some .rankInit, ((ambient, false), none), second⟩ := by
    simpa [first, frame, howner, encodeWord_length, second] using copyOwner
  have init : (advance (TM2.step program))^[1]
      (some ⟨some .rankInit, ((ambient, false), none), second⟩) =
      some ⟨some (.rank .queryFirst), ((ambient, false), none), queryFrame data v x⟩ := by
    have ht : Function.update second (.inl 3) (false :: second (.inl 3)) =
        queryFrame data v x := by
      funext j
      cases j with
      | inl j => fin_cases j <;>
          simp_all [queryFrame, second, first, frame, rankQuery,
            MachineCloudRank.queryWord, encodeWord]
      | inr j => cases j <;> rfl
    simp only [Function.iterate_one, advance_some, TM2.step, program, TM2.stepAux, ht]
  exact join_trace (join_trace firstRun secondRun) init

def rankData (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) (data : Data) : Data :=
  { data with localRank := encodeWord (PreprocessingCloudIndex.cloudRank t v e).val }

def rankRemainder (t : GraphTables.Table)
    (v : Fin t.vertices) (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) : List Bool :=
  encodeWords (((MachineCloudCount.tableRows t).drop e.val.val).flatMap MachineCloudCount.rowWords)

def rankSteps (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) : Nat :=
  querySteps v.val e.val.val +
    MachineCloudRank.rankSteps t.vertices t.darts v.val e.val.val (MachineCloudCount.tableRows t) [] +
    ((rankQuery v.val e.val.val).length + 1) + ((rankRemainder t v e).length + 1) + 2

theorem rankTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) (data : Data)
    (htable : data.table = GraphTables.tableBits t)
    (howner : data.owner = encodeWord v.val) (hindex : data.globalIndex = encodeWord e.val.val)
    (hrank : data.localRank = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[rankSteps t v e]
      (some (cfg (some .copyXFirst) data ambient register)) =
      some (cfg (some (.prefixCode .init)) (rankData t v e data) ambient none) := by
  have query := queryTrace data v.val e.val.val howner hindex hrank ambient register
  have raw := MachineCloudRank.cloudRankTrace t v e [] [] ambient none
  simp only [List.append_nil] at raw
  let mid := MachineCloudPadding.Placement.tapes rankView
    (MachineCloudCount.memory (GraphTables.tableBits t) (rankRemainder t v e)
      (rankQuery v.val e.val.val) []
      (encodeWord (PreprocessingCloudIndex.cloudRank t v e).val) (encodeWord 0)) (frame data)
  have placed := MachineCloudPadding.Placement.trace rankTape rankView rankView_left
    rankView_right Label.rank (some .rankClearQuery) (frame data)
    MachineCloudRank.rankProgram program (fun _ => rfl)
    (MachineCloudRank.rankSteps t.vertices t.darts v.val e.val.val (MachineCloudCount.tableRows t) [])
    _ _ raw
  have hstart : MachineCloudPadding.Placement.tapes rankView
      (MachineCloudCount.memory (GraphTables.tableBits t) []
        (rankQuery v.val e.val.val) [] (encodeWord 0) []) (frame data) =
      queryFrame data v.val e.val.val := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [htable, MachineCloudPadding.Placement.tapes, rankView, frame,
          queryFrame, MachineCloudCount.memory]
    | inr j => cases j <;> rfl
  simp only [rankQuery] at hstart
  have phase : (advance (TM2.step program))^[
      MachineCloudRank.rankSteps t.vertices t.darts v.val e.val.val (MachineCloudCount.tableRows t) []]
      (some ⟨some (.rank .queryFirst), ((ambient, false), none), queryFrame data v.val e.val.val⟩) =
      some ⟨some .rankClearQuery, ((ambient, false), none), mid⟩ := by
    simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
      hstart, mid, rankQuery, rankRemainder] using placed
  have first := drainAt (.inl 9) .rankClearQuery (some .rankClearWork) rfl mid ambient none
  have second := drainAt (.inl 10) .rankClearWork (some .rankClearFuel) rfl
    (Function.update mid (.inl 9) []) ambient none
  have third := drainAt (.inl 12) .rankClearFuel (some (.prefixCode .init)) rfl
    (Function.update (Function.update mid (.inl 9) []) (.inl 10) []) ambient none
  have hquery : mid (.inl 9) = rankQuery v.val e.val.val := rfl
  have hwork : Function.update mid (.inl 9) [] (.inl 10) = rankRemainder t v e := by
    simp [mid, MachineCloudPadding.Placement.tapes, rankView, MachineCloudCount.memory]
  have hfuel : ((Function.update (Function.update mid (.inl 9) []) (.inl 10) [])
      (.inl 12)).length + 1 = 2 := by
    simp [mid, MachineCloudPadding.Placement.tapes, rankView, MachineCloudCount.memory,
      encodeWord_length]
  have hfinish : Function.update
      (Function.update (Function.update mid (.inl 9) []) (.inl 10) []) (.inl 12) [] =
      frame (rankData t v e data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [htable, mid, MachineCloudPadding.Placement.tapes, rankView, frame, rankData,
          MachineCloudCount.memory]
    | inr j => cases j <;> rfl
  rw [hquery] at first
  rw [hwork] at second
  rw [hfuel, hfinish] at third
  exact join_trace (join_trace (join_trace (join_trace query phase) first) second) third

def originalMember (t : GraphTables.Table) (e : Fin t.darts) :
    DegreeReplacement.Cloud (GraphTables.semantics t) t.rows[e].tail := ⟨e, rfl⟩

def originalData (t : GraphTables.Table) (e : Fin t.darts) (data : Data) : Data :=
  cloudData t t.rows[e].tail (prefixData t t.rows[e].tail
    (rankData t t.rows[e].tail (originalMember t e) (ownerData t e data)))

def totalTime (t : GraphTables.Table) (e : Fin t.darts) : Nat :=
  ownerSteps t e + rankSteps t t.rows[e].tail (originalMember t e) +
    prefixSteps t t.rows[e].tail + MachineCloudPadding.totalTime t t.rows[e].tail

theorem originalTrace (t : GraphTables.Table) (e : Fin t.darts) (data : Data)
    (htable : data.table = GraphTables.tableBits t)
    (hindex : data.globalIndex = encodeWord e.val)
    (howner : data.owner = []) (hrank : data.localRank = []) (hcount : data.count = [])
    (hoffset : data.offset = []) (hpadding : data.padding = []) (hlevel : data.level = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime t e]
      (some (cfg (some (.owner .seed)) data ambient register)) =
      some (cfg none (originalData t e data) ambient none) := by
  have own := ownerTrace t e data htable hindex howner ambient register
  have rank := rankTrace t t.rows[e].tail (originalMember t e) (ownerData t e data)
    htable rfl hindex hrank ambient none
  have pref := prefixTrace t t.rows[e].tail
    (rankData t t.rows[e].tail (originalMember t e) (ownerData t e data))
    htable rfl hoffset ambient none
  have cloud := cloudTrace t t.rows[e].tail
    (prefixData t t.rows[e].tail
      (rankData t t.rows[e].tail (originalMember t e) (ownerData t e data)))
    htable rfl hcount hpadding hlevel ambient none
  exact join_trace (join_trace (join_trace own rank) pref) cloud

private theorem encodeWords_drop_length_le (values : List Nat) (n : Nat) :
    (encodeWords (values.drop n)).length ≤ (encodeWords values).length := by
  have h := congrArg (fun words : List Nat => (encodeWords words).length)
    (List.take_append_drop n values)
  simp only [encodeWords_append, List.length_append] at h
  omega

theorem ownerRemainder_length_le (t : GraphTables.Table) (e : Fin t.darts) :
    (ownerRemainder t e).length ≤ (GraphTables.tableBits t).length :=
  encodeWords_drop_length_le _ _

theorem rankRemainder_length_le (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) :
    (rankRemainder t v e).length ≤ (GraphTables.tableBits t).length := by
  have split := congrArg List.length
    (MachineCloudRank.encoded_rows_split (MachineCloudCount.tableRows t) e.val.val)
  have input := MachineCloudCount.inputWord_length t.vertices t.darts (MachineCloudCount.tableRows t)
  rw [MachineCloudCount.tableRows_input] at input
  simp only [List.length_append] at split
  unfold rankRemainder
  omega

noncomputable def timePolynomial : Polynomial Nat :=
  (MachineCloudPrefix.timePolynomial + MachineCloudPadding.timePolynomial).comp
      (2 * Polynomial.X) + 40 * (Polynomial.X + 1)

def overhead (N x v : Nat) : Nat :=
  (2*x + 5*N + 6) + 2 + (N+1) + 2*(x+2) + 2*(v+2) + 1 +
    (5*N + 3*(v+x+2) + 6) + (v+x+3) + (N+1) + 2 + (v+2) + 2

theorem overhead_le (N x v : Nat) (hx : x ≤ N) (hv : v ≤ N) :
    overhead N x v ≤ 40*(N+1) := by
  unfold overhead
  omega

theorem totalTime_le (t : GraphTables.Table) (e : Fin t.darts) :
    totalTime t e ≤ timePolynomial.eval (GraphTables.tableBits t).length := by
  let v := t.rows[e].tail
  let c := originalMember t e
  let N := (GraphTables.tableBits t).length
  have hn := GraphTables.vertices_le_tableBits_length t
  have hm := GraphTables.darts_le_tableBits_length t
  have hv : v.val < N := lt_of_lt_of_le v.isLt hn
  have hx : e.val ≤ N := e.isLt.le.trans hm
  have ownerBound := MachineAffineLookup.steps_le (GraphTables.tableWords t)
    e.val 4098 2 t.rows[e].tail.val (selected_owner t e)
  have ownerRest := ownerRemainder_length_le t e
  have rankBound := MachineCloudRank.rankSteps_le t.vertices t.darts v.val e.val
    (MachineCloudCount.tableRows t) []
  rw [MachineCloudCount.tableRows_input] at rankBound
  have rankRest := rankRemainder_length_le t v c
  have hpIn : MachineCloudPrefix.inputLength t v.val [] ≤ 2*N := by
    simp only [MachineCloudPrefix.inputLength, List.append_nil, encodeWord_length]
    omega
  have hcIn : MachineCloudPadding.inputLength t v [] ≤ 2*N := by
    simp only [MachineCloudPadding.inputLength, List.append_nil, encodeWord_length]
    omega
  have hp := (MachineCloudPrefix.totalTime_le t v.val v.isLt.le []).trans
    (natPolynomial_eval_mono MachineCloudPrefix.timePolynomial hpIn)
  have hc := (MachineCloudPadding.totalTime_le t v []).trans
    (natPolynomial_eval_mono MachineCloudPadding.timePolynomial hcIn)
  have ho := overhead_le N e.val v.val hx hv.le
  have hsmall : ownerSteps t e + rankSteps t v c + (v.val+2) + 2 ≤
      overhead N e.val v.val := by
    simp only [MachineCloudRank.queryWord, List.length_append, encodeWord_length,
      List.length_nil] at rankBound
    simp only [ownerSteps, rankSteps, querySteps, rankQuery, MachineCloudRank.queryWord,
      List.length_append, encodeWord_length, List.length_nil, overhead]
    change _ ≤ _ at ownerBound
    dsimp only [c, originalMember] at rankRest ⊢
    change MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 2 ≤
      2*e.val+5*N+6 at ownerBound
    omega
  have htotal : totalTime t e = ownerSteps t e + rankSteps t v c +
      MachineCloudPrefix.totalTime t v.val [] + (v.val+2) + 2 +
        MachineCloudPadding.totalTime t v := by
    simp only [totalTime, prefixSteps, v, c]
    omega
  rw [htotal]
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
  change _ ≤ MachineCloudPrefix.timePolynomial.eval (2*N) +
    MachineCloudPadding.timePolynomial.eval (2*N) + 40*(N+1)
  omega

def originalInTime (t : GraphTables.Table) (e : Fin t.darts) (data : Data)
    (htable : data.table = GraphTables.tableBits t)
    (hindex : data.globalIndex = encodeWord e.val)
    (howner : data.owner = []) (hrank : data.localRank = []) (hcount : data.count = [])
    (hoffset : data.offset = []) (hpadding : data.padding = []) (hlevel : data.level = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (cfg (some (.owner .seed)) data ambient register)
      (some (cfg none (originalData t e data) ambient none))
      (timePolynomial.eval (GraphTables.tableBits t).length) where
  steps := totalTime t e
  evals_in_steps := originalTrace t e data htable hindex howner hrank hcount hoffset
    hpadding hlevel ambient register
  steps_le_m := totalTime_le t e

def cloudInTime (t : GraphTables.Table) (v : Fin t.vertices) (data : Data)
    (htable : data.table = GraphTables.tableBits t) (howner : data.owner = encodeWord v.val)
    (hcount : data.count = []) (hpadding : data.padding = []) (hlevel : data.level = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (cfg (some (.cloud .init)) data ambient register)
      (some (cfg none (cloudData t v data) ambient none))
      (MachineCloudPadding.timePolynomial.eval (MachineCloudPadding.inputLength t v [])) where
  steps := MachineCloudPadding.totalTime t v
  evals_in_steps := cloudTrace t v data htable howner hcount hpadding hlevel ambient register
  steps_le_m := MachineCloudPadding.totalTime_le t v []

end BinPackingGames.Foundations.Complexity.MachineRegularMetadata

namespace BinPackingGames.Foundations.Complexity.MachineRegularExecutionBounds

open Turing MachineComposition PCP PCP.PreprocessingRegularTables PCP.PreprocessingCloudIndex
open PCP.PreprocessingMachineBounds MachineRegularInternalRow

theorem coreTimeBound_mono (q L R x v i k o m O L' R' x' v' i' k' o' m' O' : Nat)
    (hL : L ≤ L') (hR : R ≤ R') (hx : x ≤ x') (hv : v ≤ v') (hi : i ≤ i')
    (hk : k ≤ k') (ho : o ≤ o') (hm : m ≤ m') (hO : O ≤ O') :
    coreTimeBound q L R x v i k o m O ≤ coreTimeBound q L' R' x' v' i' k' o' m' O' := by
  unfold coreTimeBound
  gcongr

noncomputable def corePolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C (5*q+32) * rotorPolynomial q + 10 * Polynomial.X +
    2 * (Polynomial.C ExpanderFamily.growth * Polynomial.X) + 13 * Polynomial.X +
    5 * Polynomial.X + Polynomial.C (5*q+10) *
      (Polynomial.X + Polynomial.C ExpanderFamily.growth * Polynomial.X) +
    4 * (Polynomial.C ExpanderFamily.growth * Polynomial.X) +
    2 * regularPolynomial + Polynomial.C (8*q+41066)

theorem corePolynomial_eval (q L : Nat) :
    (corePolynomial q).eval L =
      coreTimeBound q L ((rotorPolynomial q).eval L)
        (ExpanderFamily.growth*L) L (ExpanderFamily.growth*L) L
        (ExpanderFamily.growth*L) L (regularPolynomial.eval L) := by
  simp only [corePolynomial, coreTimeBound, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

theorem internal_steps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding t v) q)
    (v : Fin t.vertices) (x : PaddedCloud t (padding t) v) (p : Fin q)
    (outputLength : Nat) (houtput : outputLength ≤ regularPolynomial.eval (inputLength t)) :
    coreSteps t (padding t) tables v x p outputLength ≤
      (corePolynomial q).eval (inputLength t) := by
  have hx : (vertexOrder t (padding t) x.val).val ≤ ExpanderFamily.growth * inputLength t :=
    (vertexOrder t (padding t) x.val).isLt.le.trans (regularVertices_le_input t)
  have hi : (paddedCloudRank t (padding t) v x).val ≤ ExpanderFamily.growth * inputLength t :=
    (paddedCloudRank t (padding t) v x).isLt.le.trans (cloudTotal_le_input t v)
  have hv : v.val ≤ inputLength t :=
    v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hm : t.darts ≤ inputLength t := GraphTables.darts_le_tableBits_length t
  rw [corePolynomial_eval]
  exact (coreSteps_le q positive t (padding t) tables v x p outputLength).trans
    (coreTimeBound_mono q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ le_rfl
      (cloudRotorBits_le t v (tables v)) hx hv hi (cloudSize_le_input t v)
      (prefix_le_input t v.val) hm houtput)

noncomputable def familyPolynomial : Polynomial Nat :=
  MachinePaddedExpanderFamilyBounds.timePolynomial.comp (Polynomial.X + 1) +
    Polynomial.C (2 * ExpanderFamily.growth) * (Polynomial.X + 1) + 7

theorem family_budget_le (t : GraphTables.Table) (v : Fin t.vertices) :
    MachinePaddedExpanderFamilyBounds.timePolynomial.eval (cloudSize t v + 1) +
      2 * ExpanderFamily.growth * (cloudSize t v + 1) + 7 ≤
        familyPolynomial.eval (inputLength t) := by
  have h := Nat.add_le_add_right (cloudSize_le_input t v) 1
  have hp := natPolynomial_eval_mono MachinePaddedExpanderFamilyBounds.timePolynomial h
  have hm := Nat.mul_le_mul_left (2 * ExpanderFamily.growth) h
  simp only [familyPolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_ofNat]
  omega

noncomputable def rowPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C ExpanderFamily.growth * Polynomial.X +
    (Polynomial.C ExpanderFamily.growth * Polynomial.X) * Polynomial.C (q + 1) + 8192

theorem rowPolynomial_eval (q L : Nat) :
    (rowPolynomial q).eval L =
      ExpanderFamily.growth * L + (ExpanderFamily.growth * L) * (q + 1) + 8192 := by
  simp only [rowPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]

theorem actual_row_bound_le (q : Nat) (t : GraphTables.Table) :
    vertexCount t (padding t) + vertexCount t (padding t) * (q + 1) + 8192 ≤
      (rowPolynomial q).eval (inputLength t) := by
  rw [rowPolynomial_eval]
  have h := regularVertices_le_input t
  exact Nat.add_le_add_right (Nat.add_le_add h (Nat.mul_le_mul_right _ h)) _

noncomputable def blockCorePolynomial (q : Nat) : Polynomial Nat :=
  corePolynomial q + Polynomial.C (2*q) * rowPolynomial q

theorem coreTimeBound_add_output (q L R x v i k o m O A : Nat) :
    coreTimeBound q L R x v i k o m (O + A) =
      coreTimeBound q L R x v i k o m O + 2*A := by
  unfold coreTimeBound
  omega

theorem block_core_bound_le (q : Nat) (t : GraphTables.Table)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding t v) q)
    (v : Fin t.vertices) (x : PaddedCloud t (padding t) v)
    (initialOutput : Nat) (houtput : initialOutput ≤ regularPolynomial.eval (inputLength t)) :
    coreTimeBound q (GraphTables.tableBits t).length
      (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
      (vertexOrder t (padding t) x.val).val v.val (paddedCloudRank t (padding t) v x).val
      (cloudSize t v) (PreprocessingPaddingOffsets.offset (padding t) v.val) t.darts
      (initialOutput + q *
        (vertexCount t (padding t) + vertexCount t (padding t) * (q + 1) + 8192)) ≤
      (blockCorePolynomial q).eval (inputLength t) := by
  have hx : (vertexOrder t (padding t) x.val).val ≤ ExpanderFamily.growth * inputLength t :=
    (vertexOrder t (padding t) x.val).isLt.le.trans (regularVertices_le_input t)
  have hi : (paddedCloudRank t (padding t) v x).val ≤ ExpanderFamily.growth * inputLength t :=
    (paddedCloudRank t (padding t) v x).isLt.le.trans (cloudTotal_le_input t v)
  have hv : v.val ≤ inputLength t :=
    v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hm : t.darts ≤ inputLength t := GraphTables.darts_le_tableBits_length t
  have hr := Nat.mul_le_mul_left q (actual_row_bound_le q t)
  have hO := Nat.add_le_add houtput hr
  have h := coreTimeBound_mono q (inputLength t) _ _ _ _ _ _ _ _
    (inputLength t) _ _ _ _ _ _ _ _ le_rfl
    (cloudRotorBits_le t v (tables v)) hx hv hi (cloudSize_le_input t v)
    (prefix_le_input t v.val) hm hO
  simp only [coreTimeBound_add_output] at h ⊢
  rw [← corePolynomial_eval] at h
  simpa only [inputLength, blockCorePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Nat.mul_assoc] using h

end BinPackingGames.Foundations.Complexity.MachineRegularExecutionBounds

end OAI
