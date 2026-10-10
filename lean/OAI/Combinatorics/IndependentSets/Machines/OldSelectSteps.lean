import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineCloudPadding
import OAI.Combinatorics.IndependentSets.Machines.SelectAlphabet

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow
open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
variable {K Λ σ : Type} [DecidableEq K]

def oldSelectSteps (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) : Nat :=
  (2 * (i.val + 1) + 1) + (2 * (v.val + 1) + 1) +
    MachineCloudSelect.cloudSelectSteps t v i [] + (v.val + i.val + 7)

theorem selectOldTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (o : Nat) (ambient : σ) :
    (advance (TM2.step selectProgram))^[oldSelectSteps t v i]
      (some ⟨some (.inr (.copy .oldLocal .seed)), selectCleanState ambient none,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v) o t.darts [] [] [] [] [] []⟩) =
      some ⟨none, selectCleanState ambient none,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v) o t.darts []
          (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val) [] [] [] []⟩ := by
  let graph := GraphTables.tableBits t
  let k := PreprocessingCloudIndex.cloudSize t v
  have hi := selectCopyTrace .oldLocal
    (selectMemory graph i.val v.val k o t.darts [] [] [] [] [] [])
    i.val rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_query, update_selectMemory_query, List.append_nil] at hi
  have hv := selectCopyTrace .oldOwner
    (selectMemory graph i.val v.val k o t.darts (encodeWord i.val) [] [] [] [] [])
    v.val rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_query, update_selectMemory_query] at hv
  have hc := selectCloudTrace t v i (selectExtraMemory i.val v.val k o t.darts [] [] [] [])
    ambient none
  have hq : MachineCloudSelect.queryWord v.val i.val [] =
      encodeWord v.val ++ encodeWord i.val := by
    simp only [MachineCloudSelect.queryWord, MachineCloudRank.queryWord, List.append_nil]
  change (advance (TM2.step selectProgram))^[MachineCloudSelect.cloudSelectSteps t v i []]
    (some ⟨some (.inl (.inr .initialize)), selectCleanState ambient none,
      selectMemory graph i.val v.val k o t.darts
        (MachineCloudSelect.queryWord v.val i.val []) [] [] [] [] []⟩) =
    some ⟨some (.inr (.cleanup 0)), selectCleanState ambient none,
      selectMemory graph i.val v.val k o t.darts
        (MachineCloudSelect.queryWord v.val i.val [])
        (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val) [] [] [] []⟩ at hc
  rw [hq] at hc
  have hd := selectCleanupTrace graph i.val v.val k o t.darts
    (encodeWord v.val ++ encodeWord i.val)
    (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val) [] [] [] [] ambient
  have hn : (encodeWord v.val ++ encodeWord i.val).length + ([] : List Bool).length + ([] : List Bool).length +
      ([] : List Bool).length + ([] : List Bool).length + 5 = v.val + i.val + 7 := by
    simp only [List.length_append, encodeWord_length, List.length_nil]
    omega
  rw [hn] at hd
  exact joinTrace (joinTrace (joinTrace hi hv) hc) hd

def dummySelectSteps (j k o m : Nat) : Nat :=
  (2 * (j + 1) + 1) + (2 * (k + 1) + 1) + (k + 1) +
    (2 * (j - k + 1) + 1) + 2 * (o + 1) + 2 * (m + 1) + (j + k + 7)

theorem dummySelectSteps_eq (j k o m : Nat) (h : k ≤ j) :
    dummySelectSteps j k o m = 5 * j + 2 * k + 2 * o + 2 * m + 21 := by
  unfold dummySelectSteps
  omega

theorem selectDummyTrace (graph : List Bool) (j v k o m : Nat) (hk : k ≤ j)
    (ambient : σ) :
    (advance (TM2.step selectProgram))^[dummySelectSteps j k o m]
      (some ⟨some (.inr (.copy .dummyLocal .seed)), selectCleanState ambient none,
        selectMemory graph j v k o m [] [] [] [] [] []⟩) =
      some ⟨none, selectCleanState ambient none,
        selectMemory graph j v k o m [] (encodeWord (m + o + (j - k))) [] [] [] []⟩ := by
  have hjcopy := selectCopyTrace .dummyLocal
    (selectMemory graph j v k o m [] [] [] [] [] []) j rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_extra, selectExtraMemory,
    update_selectMemory_local, List.append_nil] at hjcopy
  have hkcopy := selectCopyTrace .dummySize
    (selectMemory graph j v k o m [] [] [] [] (encodeWord j) []) k rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_extra, selectExtraMemory,
    update_selectMemory_size, List.append_nil] at hkcopy
  have scanFrame (left right savedLeft savedRight : List Bool) :
      MachineUnaryLessAt.tapes subtractSlots
        (selectMemory graph j v k o m [] [] [] [] [] [])
        left right savedLeft savedRight =
      selectMemory graph j v k o m [] [] savedLeft savedRight left right := by
    simp only [MachineUnaryLessAt.tapes,
      show subtractSlots 0 = .inr .localWork from rfl,
      show subtractSlots 1 = .inr .sizeWork from rfl,
      show subtractSlots 2 = .inr .savedLeft from rfl,
      show subtractSlots 3 = .inr .savedRight from rfl,
      update_selectMemory_local, update_selectMemory_size,
      update_selectMemory_left, update_selectMemory_right]
  have hscan := MachineUnaryLessAt.scanTrace subtractSlots (.inr .subtract)
    (.inr (.copy .dummyDifference .seed)) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] [] [] [] [] [])
    j k [] [] [] [] (ambient, MachineCloudSelect.Phase.checking) false none
  simp only [List.append_nil, scanFrame, Nat.min_eq_right hk, Nat.sub_eq_zero_of_le hk,
    show ¬ j < k from Nat.not_lt_of_ge hk, decide_false] at hscan
  have hdiffcopy := selectCopyTrace .dummyDifference
    (selectMemory graph j v k o m [] [] (List.replicate k true) (List.replicate k true)
      (encodeWord (j - k)) (encodeWord 0)) (j - k) rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_output, update_selectMemory_output, List.append_nil] at hdiffcopy
  have hprefix := selectAddTrace .prefixOffset
    (selectMemory graph j v k o m [] (encodeWord (j - k))
      (List.replicate k true) (List.replicate k true) (encodeWord (j - k)) (encodeWord 0))
    o (j - k) rfl rfl rfl ambient
  simp only [afterAdd, update_selectMemory_output] at hprefix
  have hm := selectAddTrace .darts
    (selectMemory graph j v k o m [] (encodeWord (o + (j - k)))
      (List.replicate k true) (List.replicate k true) (encodeWord (j - k)) (encodeWord 0))
    m (o + (j - k)) rfl rfl rfl ambient
  simp only [afterAdd, update_selectMemory_output, ← Nat.add_assoc] at hm
  have hcleanup := selectCleanupTrace graph j v k o m []
    (encodeWord (m + o + (j - k))) (List.replicate k true) (List.replicate k true)
    (encodeWord (j - k)) (encodeWord 0) ambient
  have hcleanSteps : ([] : List Bool).length + (encodeWord (j - k)).length + (encodeWord 0).length +
      (List.replicate k true).length + (List.replicate k true).length + 5 = j + k + 7 := by
    simp only [List.length_nil, encodeWord_length, List.length_replicate]
    omega
  rw [hcleanSteps] at hcleanup
  exact joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    hjcopy hkcopy) hscan) hdiffcopy) hprefix) hm) hcleanup

def selectionSteps (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (PreprocessingCloudIndex.cloudSize t v + padding v)) : Nat :=
  MachineUnaryLessAt.steps i.val (PreprocessingCloudIndex.cloudSize t v) + 1 +
    if hi : i.val < PreprocessingCloudIndex.cloudSize t v then
      oldSelectSteps t v ⟨i.val, hi⟩
    else dummySelectSteps i.val (PreprocessingCloudIndex.cloudSize t v)
      (PreprocessingPaddingOffsets.offset padding v.val) t.darts

theorem selectionTrace (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (PreprocessingCloudIndex.cloudSize t v + padding v))
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[selectionSteps t padding v i]
      (some ⟨some (.inr (.compare .scan)), selectCleanState ambient register,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v)
          (PreprocessingPaddingOffsets.offset padding v.val) t.darts [] [] [] [] [] []⟩) =
      some ⟨none, selectCleanState ambient none,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v)
          (PreprocessingPaddingOffsets.offset padding v.val) t.darts []
          (encodeWord (PreprocessingInternalRows.selectedIndex t padding v i)) [] [] [] []⟩ := by
  have hc := selectComparisonTrace
    (selectMemory (GraphTables.tableBits t) i.val v.val
      (PreprocessingCloudIndex.cloudSize t v)
      (PreprocessingPaddingOffsets.offset padding v.val) t.darts [] [] [] [] [] [])
    i.val (PreprocessingCloudIndex.cloudSize t v) rfl rfl rfl rfl ambient register
  by_cases hi : i.val < PreprocessingCloudIndex.cloudSize t v
  · simp only [ite_eq_left hi] at hc
    have hb := selectOldTrace t v ⟨i.val, hi⟩
      (PreprocessingPaddingOffsets.offset padding v.val) ambient
    simpa only [selectionSteps, dite_eq_left hi,
      PreprocessingInternalRows.selectedIndex_old t padding v i hi] using joinTrace hc hb
  · simp only [ite_eq_right hi] at hc
    have hb := selectDummyTrace (GraphTables.tableBits t) i.val v.val
      (PreprocessingCloudIndex.cloudSize t v)
      (PreprocessingPaddingOffsets.offset padding v.val) t.darts (Nat.le_of_not_gt hi) ambient
    simpa only [selectionSteps, dite_eq_right hi,
      PreprocessingInternalRows.selectedIndex_dummy t padding v i (Nat.le_of_not_gt hi)]
      using joinTrace hc hb

theorem selectionSteps_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (PreprocessingCloudIndex.cloudSize t v + padding v)) :
    selectionSteps t padding v i ≤
      10 * (GraphTables.tableBits t).length + 16 * i.val + 13 * v.val +
      5 * PreprocessingCloudIndex.cloudSize t v +
      2 * PreprocessingPaddingOffsets.offset padding v.val + 2 * t.darts + 57 := by
  unfold selectionSteps
  split
  · rename_i hi
    have hb := MachineCloudSelect.cloudSelectSteps_le t v ⟨i.val, hi⟩ []
    have hmin : min i.val (PreprocessingCloudIndex.cloudSize t v) = i.val := Nat.min_eq_left hi.le
    simp only [oldSelectSteps, MachineUnaryLessAt.steps, hmin]
    simp only [MachineCloudSelect.queryWord, MachineCloudRank.queryWord,
      List.length_append, encodeWord_length, List.length_nil] at hb
    omega
  · rename_i hi
    rw [dummySelectSteps_eq _ _ _ _ (Nat.le_of_not_gt hi)]
    have hmin := Nat.min_le_right i.val (PreprocessingCloudIndex.cloudSize t v)
    unfold MachineUnaryLessAt.steps
    omega

def selectorMachine : FinTM2 where
  K := SelectTape
  k₀ := .inl (.inl .original)
  k₁ := selectOutput
  Γ := SelectAlphabet
  Λ := SelectLabel
  main := .inr (.compare .scan)
  σ := SelectState Unit
  initialState := selectCleanState () none
  m := selectProgram

def selectionInTime (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (PreprocessingCloudIndex.cloudSize t v + padding v))
    (register : Option Bool) :
    StateTransition.EvalsToInTime selectorMachine.step
      ⟨some (.inr (.compare .scan)), selectCleanState () register,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v)
          (PreprocessingPaddingOffsets.offset padding v.val) t.darts [] [] [] [] [] []⟩
      (some ⟨none, selectCleanState () none,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v)
          (PreprocessingPaddingOffsets.offset padding v.val) t.darts []
          (encodeWord (PreprocessingInternalRows.selectedIndex t padding v i)) [] [] [] []⟩)
      (10 * (GraphTables.tableBits t).length + 16 * i.val + 13 * v.val +
        5 * PreprocessingCloudIndex.cloudSize t v +
        2 * PreprocessingPaddingOffsets.offset padding v.val + 2 * t.darts + 57) where
  steps := selectionSteps t padding v i
  evals_in_steps := selectionTrace t padding v i () register
  steps_le_m := selectionSteps_le t padding v i

def coreRotorTapes : Fin 8 → CoreTape := ![3, 7, 10, 11, 12, 9, 13, 14]

def coreFinishTapes : Fin 8 → CoreTape := ![1, 15, 14, 9, 24, 25, 26, 8]

def coreSelectTape : SelectTape → CoreTape
  | .inl (.inl .original) => 0
  | .inl (.inl .work) => 17
  | .inl (.inl .target) => 16
  | .inl (.inl .scratch) => 9
  | .inl (.inl .count) => 18
  | .inl (.inl .spare) => 19
  | .inl (.inr ()) => 15
  | .inr .localIndex => 13
  | .inr .owner => 2
  | .inr .cloudSize => 4
  | .inr .prefixOffset => 5
  | .inr .darts => 6
  | .inr .savedLeft => 20
  | .inr .savedRight => 21
  | .inr .localWork => 22
  | .inr .sizeWork => 23

def coreSelectView : CoreTape → Option SelectTape :=
  ![some (.inl (.inl .original)), none, some (.inr .owner), none,
    some (.inr .cloudSize), some (.inr .prefixOffset), some (.inr .darts), none, none,
    some (.inl (.inl .scratch)), none, none, none, some (.inr .localIndex), none,
    some (.inl (.inr ())), some (.inl (.inl .target)), some (.inl (.inl .work)),
    some (.inl (.inl .count)), some (.inl (.inl .spare)),
    some (.inr .savedLeft), some (.inr .savedRight),
    some (.inr .localWork), some (.inr .sizeWork), none, none, none]

theorem coreSelectView_left (k : SelectTape) : coreSelectView (coreSelectTape k) = some k := by
  cases k with
  | inl k =>
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k; rfl
  | inr k => cases k <;> rfl

theorem coreSelectView_right (j : CoreTape) (k : SelectTape)
    (h : coreSelectView j = some k) : coreSelectTape k = j := by
  fin_cases j <;> simp [coreSelectView] at h
  all_goals subst k; rfl

def coreCleanupTape : Fin 10 → CoreTape := ![10, 11, 12, 13, 14, 15, 9, 16, 17, 18]

def coreRotorStateEquiv (σ : Type) (q : Nat) :
    MachineFixedDivMod.State
      ((σ × MachineFixedBlockMap.Buffer 4096) × (Bool × MachineCloudSelect.Phase)) q ≃
        CoreState σ q where
  toFun s := ((s.1.1.1.1, (s.1.1.1.2, (s.1.2, s.1.1.2))), s.2)
  invFun s := ((((s.1.1, s.1.2.1), s.1.2.2.2), s.1.2.2.1), s.2)
  left_inv s := by rcases s with ⟨⟨⟨⟨a,b⟩,⟨c,d⟩⟩,e⟩,f⟩; rfl
  right_inv s := by rcases s with ⟨⟨a,⟨b,⟨c,⟨d,e⟩⟩⟩⟩,f⟩; rfl

def coreSelectStateEquiv (σ : Type) (q : Nat) :
    SelectState (σ × (MachineFixedBlockMap.Buffer 4096 × Fin q)) ≃ CoreState σ q where
  toFun s := ((s.1.1.1.1, (s.1.1.1.2.1, (s.1.1.1.2.2, (s.1.2, s.1.1.2)))), s.2)
  invFun s := ((((s.1.1, (s.1.2.1, s.1.2.2.1)), s.1.2.2.2.2), s.1.2.2.2.1), s.2)
  left_inv s := by rcases s with ⟨⟨⟨⟨a,⟨b,c⟩⟩,d⟩,e⟩,f⟩; rfl
  right_inv s := by rcases s with ⟨⟨a,⟨b,⟨c,⟨d,e⟩⟩⟩⟩,f⟩; rfl

def coreAfterCleanup {q : Nat} (labels : CoreLabel q → Λ) (exit : Option Λ) (i : Fin 10) :
    Option Λ :=
  if h : i.val + 1 < 10 then some (labels (.cleanup ⟨i.val + 1,h⟩)) else exit

def coreInstruction (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ) :
    CoreLabel q → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q)
  | .rotor stage => MachineStateEquiv.statement (coreRotorStateEquiv σ q)
      (rotorInstruction q positive p coreRotorTapes
        (fun l => labels (.rotor l)) (some (labels (.select (.inr (.compare .scan))))) stage)
  | .select stage => MachineCloudPadding.Placement.statement coreSelectTape
      (fun l => labels (.select l)) (some (labels (.finish .seedReturn)))
      (MachineStateEquiv.statement (coreSelectStateEquiv σ q) (selectProgram stage))
  | .finish stage => finishInstruction q coreFinishTapes
      (fun l => labels (.finish l)) (some (labels (.cleanup 0))) stage
  | .cleanup i => MachineDrain.drain (coreCleanupTape i) (labels (.cleanup i))
      (coreAfterCleanup labels exit i)

def coreInitialState (q : Nat) (positive : 0 < q) (ambient : σ) : CoreState σ q :=
  ((ambient, (MachineFixedBlockMap.emptyBuffer 4096,
    (MachineFixedDivMod.residue q positive 0, (false, MachineCloudSelect.Phase.checking)))), none)

def coreMachine (q : Nat) (positive : 0 < q) (p : Fin q) : FinTM2 where
  K := CoreTape
  k₀ := 0
  k₁ := 8
  Γ _ := Bool
  Λ := CoreLabel q
  main := coreEntry q
  σ := CoreState Unit q
  initialState := coreInitialState q positive ()
  m := coreInstruction q positive p id none

def coreMemory (graph : List Bool) (x v i k o m : Nat) (rotor output : List Bool)
    (query scan flat localIndex returnPort selected : List Bool) : CoreTape → List Bool :=
  ![graph, encodeWord x, encodeWord v, encodeWord i, encodeWord k, encodeWord o,
    encodeWord m, rotor, output, [], query, scan, flat, localIndex, returnPort, selected,
    [], [], [], [], [], [], [], [], [], [], []]

@[simp] theorem coreMemory_update_output (graph : List Bool) (x v i k o m : Nat)
    (rotor output query scan flat localIndex returnPort selected newOutput : List Bool) :
    Function.update (coreMemory graph x v i k o m rotor output query scan flat
      localIndex returnPort selected) (8 : CoreTape) newOutput =
      coreMemory graph x v i k o m rotor newOutput query scan flat localIndex returnPort selected := by
  funext z
  fin_cases z <;> rfl

theorem coreRotorTapes_injective : Function.Injective coreRotorTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coreRotorTapes]

theorem coreFinishTapes_injective : Function.Injective coreFinishTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coreFinishTapes]

def coreCleaned (base : CoreTape → List Bool) : CoreTape → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
      (Function.update base 10 []) 11 []) 12 []) 13 []) 14 []) 15 []) 9 []) 16 []) 17 []) 18 []

def coreCleanupSteps (base : CoreTape → List Bool) : Nat :=
  (base 10).length + (base 11).length + (base 12).length + (base 13).length +
  (base 14).length + (base 15).length + (base 9).length + (base 16).length +
  (base 17).length + (base 18).length + 10

theorem coreCleanupTrace (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (base : CoreTape → List Bool)
    (ambient : σ × (MachineFixedBlockMap.Buffer 4096 ×
      (Fin q × (Bool × MachineCloudSelect.Phase)))) :
    (advance (TM2.step program))^[coreCleanupSteps base]
      (some ⟨some (labels (.cleanup 0)), (ambient, none), base⟩) =
      some ⟨exit, (ambient, none), coreCleaned base⟩ := by
  let b1 := Function.update base (10 : CoreTape) []
  have h0 := MachineDrain.drainTrace (10 : CoreTape) (labels (.cleanup 0))
    (some (labels (.cleanup 1))) program (code (.cleanup 0)) base (base 10) ambient none
  rw [Function.update_eq_self] at h0
  let b2 := Function.update b1 (11 : CoreTape) []
  have h1 := MachineDrain.drainTrace (11 : CoreTape) (labels (.cleanup 1))
    (some (labels (.cleanup 2))) program (code (.cleanup 1)) b1 (b1 11) ambient none
  rw [Function.update_eq_self] at h1
  have hw1 : b1 11 = base 11 := by simp [b1]
  rw [hw1] at h1
  let b3 := Function.update b2 (12 : CoreTape) []
  have h2 := MachineDrain.drainTrace (12 : CoreTape) (labels (.cleanup 2))
    (some (labels (.cleanup 3))) program (code (.cleanup 2)) b2 (b2 12) ambient none
  rw [Function.update_eq_self] at h2
  have hw2 : b2 12 = base 12 := by simp [b1, b2]
  rw [hw2] at h2
  let b4 := Function.update b3 (13 : CoreTape) []
  have h3 := MachineDrain.drainTrace (13 : CoreTape) (labels (.cleanup 3))
    (some (labels (.cleanup 4))) program (code (.cleanup 3)) b3 (b3 13) ambient none
  rw [Function.update_eq_self] at h3
  have hw3 : b3 13 = base 13 := by simp [b1, b2, b3]
  rw [hw3] at h3
  let b5 := Function.update b4 (14 : CoreTape) []
  have h4 := MachineDrain.drainTrace (14 : CoreTape) (labels (.cleanup 4))
    (some (labels (.cleanup 5))) program (code (.cleanup 4)) b4 (b4 14) ambient none
  rw [Function.update_eq_self] at h4
  have hw4 : b4 14 = base 14 := by simp [b1, b2, b3, b4]
  rw [hw4] at h4
  let b6 := Function.update b5 (15 : CoreTape) []
  have h5 := MachineDrain.drainTrace (15 : CoreTape) (labels (.cleanup 5))
    (some (labels (.cleanup 6))) program (code (.cleanup 5)) b5 (b5 15) ambient none
  rw [Function.update_eq_self] at h5
  have hw5 : b5 15 = base 15 := by simp [b1, b2, b3, b4, b5]
  rw [hw5] at h5
  let b7 := Function.update b6 (9 : CoreTape) []
  have h6 := MachineDrain.drainTrace (9 : CoreTape) (labels (.cleanup 6))
    (some (labels (.cleanup 7))) program (code (.cleanup 6)) b6 (b6 9) ambient none
  rw [Function.update_eq_self] at h6
  have hw6 : b6 9 = base 9 := by simp [b1, b2, b3, b4, b5, b6]
  rw [hw6] at h6
  let b8 := Function.update b7 (16 : CoreTape) []
  have h7 := MachineDrain.drainTrace (16 : CoreTape) (labels (.cleanup 7))
    (some (labels (.cleanup 8))) program (code (.cleanup 7)) b7 (b7 16) ambient none
  rw [Function.update_eq_self] at h7
  have hw7 : b7 16 = base 16 := by simp [b1, b2, b3, b4, b5, b6, b7]
  rw [hw7] at h7
  let b9 := Function.update b8 (17 : CoreTape) []
  have h8 := MachineDrain.drainTrace (17 : CoreTape) (labels (.cleanup 8))
    (some (labels (.cleanup 9))) program (code (.cleanup 8)) b8 (b8 17) ambient none
  rw [Function.update_eq_self] at h8
  have hw8 : b8 17 = base 17 := by simp [b1, b2, b3, b4, b5, b6, b7, b8]
  rw [hw8] at h8
  let b10 := Function.update b9 (18 : CoreTape) []
  have h9 := MachineDrain.drainTrace (18 : CoreTape) (labels (.cleanup 9))
    exit program (code (.cleanup 9)) b9 (b9 18) ambient none
  rw [Function.update_eq_self] at h9
  have hw9 : b9 18 = base 18 := by simp [b1, b2, b3, b4, b5, b6, b7, b8, b9]
  rw [hw9] at h9
  have total := (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace h0 h1) h2) h3) h4) h5) h6) h7) h8) h9)
  have hn : coreCleanupSteps base =
      (base 10).length + 1 + ((base 11).length + 1) + ((base 12).length + 1) +
      ((base 13).length + 1) + ((base 14).length + 1) + ((base 15).length + 1) +
      ((base 9).length + 1) + ((base 16).length + 1) + ((base 17).length + 1) +
      ((base 18).length + 1) := by unfold coreCleanupSteps; omega
  rw [hn]
  exact total

end IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow

end OAI
