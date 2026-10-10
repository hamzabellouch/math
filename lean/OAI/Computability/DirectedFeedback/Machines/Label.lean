import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineRegularTable

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
namespace DFVSGames.Foundations.Complexity.MachineRegularTable
open Turing MachineComposition
open DFVSGames.Foundations.PCP
namespace Top

inductive Label
  | header (l : Header.Label)
  | oldSeed
  | copyFirst (phase : CopyPhase)
  | copySecond (phase : CopyPhase)
  | oldGuard
  | oldBody (l : MachineRegularOriginalBody.Label)
  | oldIncrement
  | ownerSeed
  | ownerGuard
  | ownerBody (l : MachineRegularOwnerBody.Label)
  | ownerIncrement
  | clear (i : Fin 7)
  deriving DecidableEq, Fintype

def copyExit : CopyPhase → Label
  | .old => .oldGuard
  | .owner => .ownerGuard

def clearTape : Fin 7 → Tape :=
  ![coreTape 1, coreTape 2, coreTape 5, coreTape 6,
    headerTape Header.nTape, headerTape Header.verticesTape, headerTape Header.dartsTape]

def clearEntry (k : Nat) : Option Label :=
  if h : k < 7 then some (.clear ⟨k, h⟩) else none

def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .header l => Lift.statement headerTape Label.header (some .oldSeed) headerStates
      (Header.program PreprocessingRegularTables.internalDegree l)
  | .oldSeed => .push (coreTape 1) (fun _ => false) (.goto fun _ => Label.copyFirst CopyPhase.old)
  | .copyFirst phase => Reduction.MachineTransfer.loopAt (copySource phase) scratch id false
      (.copyFirst phase) (some (.copySecond phase))
  | .copySecond phase => MachineCopy.forkLoop scratch (copySource phase) (copyTarget phase) false
      (.copySecond phase) (some (copyExit phase))
  | .oldGuard => Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry) (some Label.ownerSeed)
  | .oldBody l => Lift.statement Sum.inl Label.oldBody (some .oldIncrement) (Equiv.refl _)
      (MachineRegularOriginalBody.program H l)
  | .oldIncrement => Fuel.increment (coreTape 1) Label.oldGuard
  | .ownerSeed => .push (coreTape 2) (fun _ => false)
      (.push (coreTape 5) (fun _ => false) (.goto fun _ => Label.copyFirst CopyPhase.owner))
  | .ownerGuard => Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry) (clearEntry 0)
  | .ownerBody l => MachineCloudPadding.Placement.statement ownerTape Label.ownerBody
      (some .ownerIncrement) (MachineRegularOwnerBody.program H l)
  | .ownerIncrement => Fuel.increment (coreTape 2) Label.ownerGuard
  | .clear i => MachineDrain.drain (clearTape i) (.clear i) (clearEntry (i.val + 1))

def machine (H : BaseTable) : FinTM2 where
  K := Tape
  k₀ := coreTape 0
  k₁ := coreTape 8
  Γ _ := Bool
  Λ := Label
  main := .header .init
  σ := State
  initialState := readyState H
  m := program H

def frame (data : Data) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    Tape → List Bool
  | .inl k => MachineRegularOriginalBody.frame data k
  | .inr (.inl k) => header k
  | .inr (.inr i) => counters i

def cfg (H : BaseTable) (label : Option Label) (data : Data)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data header counters⟩

@[simp] theorem frame_core (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (i : Fin 27) :
    frame data header counters (coreTape i) = MachineRegularMetadata.frame data (.inl i) := rfl

theorem bodyPlacement (data extra : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) :
    MachineCloudPadding.Placement.tapes bodyView (MachineRegularOriginalBody.frame data)
      (frame extra header counters) = frame data header counters := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j <;> rfl

def headerAux (n N R : List Bool) : Header.Tape → List Bool := fun k =>
  if k = Header.nTape then n
  else if k = Header.verticesTape then N
  else if k = Header.dartsTape then R
  else []

@[simp] theorem headerAux_empty : headerAux [] [] [] = (fun _ => []) := by
  funext k
  simp [headerAux]

theorem headerPlacement (data : Data) (t n m N R output : List Bool)
    (counters : Fin 4 → List Bool) :
    MachineCloudPadding.Placement.tapes headerView
      (Header.frame t n [] [] [] m [] [] [] N R [] output)
      (frame data (fun _ => []) counters) =
      frame { data with table := t, darts := m, output := output } (headerAux n N R) counters := by
  funext j
  cases j with
  | inl j =>
    cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j =>
    cases j with
    | inl k =>
      cases k with
      | inl k =>
        cases k with
        | inner k => cases k <;> rfl
        | bound => rfl
        | remaining => rfl
        | total => rfl
      | inr k => cases k <;> rfl
    | inr i => rfl

def inputData (t : GraphTables.Table) (output : List Bool) : Data where
  table := GraphTables.tableBits t
  globalIndex := []
  owner := []
  localRank := []
  count := []
  offset := []
  darts := []
  rotor := []
  output := output
  padding := []
  level := []

def headerData (t : GraphTables.Table) (output : List Bool) : Data :=
  { inputData t output with darts := encodeWord t.darts }

def headerStacks (t : GraphTables.Table) : Header.Tape → List Bool :=
  headerAux (encodeWord t.vertices) (encodeWord (Header.vertexTotal t))
    (encodeWord (Header.dartTotal PreprocessingRegularTables.internalDegree t))

theorem headerTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[Header.totalTime PreprocessingRegularTables.internalDegree t output]
      (some (cfg H (some (.header .init)) (inputData t output) (fun _ => []) counters)) =
      some (cfg H (some .oldSeed)
        (headerData t (output ++ Header.headerBits PreprocessingRegularTables.internalDegree t))
        (headerStacks t) counters) := by
  have raw := Header.trace PreprocessingRegularTables.internalDegree t output () none
  have placed := Lift.trace headerTape headerView headerView_left headerView_right
    Label.header (some .oldSeed) headerStates
    (MachineRegularInternalRow.coreInitialState PreprocessingRegularTables.internalDegree
      MachineRegularOriginalBody.degree_positive (), (MachineRegularFamily.readyState H, none))
    (frame (inputData t output) (fun _ => []) counters)
    (Header.program PreprocessingRegularTables.internalDegree) (program H) (fun _ => rfl)
    _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, headerPlacement,
    headerAux_empty, cfg, readyState, MachineRegularOriginalBody.readyState, headerStates,
    Equiv.coe_fn_mk, headerData, inputData, headerStacks] using placed

def oldData (t : GraphTables.Table) (index : Nat) (output : List Bool) : Data :=
  { headerData t output with globalIndex := encodeWord index }

theorem originalData_eq (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) :
    MachineRegularOriginalBody.initialData t e output = oldData t e.val output := rfl

theorem oldBodyTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularOriginalBody.totalSteps H t e output]
      (some (cfg H (some (Label.oldBody MachineRegularOriginalBody.entry))
        (oldData t e.val output) header counters)) =
      some (cfg H (some .oldIncrement)
        (oldData t e.val (output ++ MachineRegularOriginalBody.emittedBits H t e)) header counters) := by
  have raw := MachineRegularOriginalBody.originalTrace H t e output
  have placed := Lift.trace Sum.inl bodyView bodyView_left bodyView_right Label.oldBody
    (some .oldIncrement) (Equiv.refl _) none
    (frame (oldData t e.val output) header counters)
    (MachineRegularOriginalBody.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, bodyPlacement,
    MachineRegularOriginalBody.cfg, originalData_eq, cfg, readyState, Equiv.refl_apply] using placed

def counterStacks (old owners dummy work : List Bool) : Fin 4 → List Bool :=
  ![old, owners, dummy, work]

@[simp] theorem frame_oldFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work : List Bool) :
    frame data header (counterStacks old owners dummy work) oldFuel = old := rfl

@[simp] theorem frame_ownerFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work : List Bool) :
    frame data header (counterStacks old owners dummy work) ownerFuel = owners := rfl

@[simp] theorem update_frame_oldFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work replacement : List Bool) :
    Function.update (frame data header (counterStacks old owners dummy work)) oldFuel replacement =
      frame data header (counterStacks replacement owners dummy work) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j with
    | inl j => rfl
    | inr i => fin_cases i <;> rfl

@[simp] theorem update_frame_ownerFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work replacement : List Bool) :
    Function.update (frame data header (counterStacks old owners dummy work)) ownerFuel replacement =
      frame data header (counterStacks old replacement dummy work) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j with
    | inl j => rfl
    | inr i => fin_cases i <;> rfl

@[simp] theorem update_frame_global (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 1) replacement =
      frame { data with globalIndex := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_owner (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 2) replacement =
      frame { data with owner := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

theorem oldGuardStep (H : BaseTable) (data : Data) (header : Header.Tape → List Bool)
    (remaining : Nat) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldGuard) data header
        (counterStacks (encodeWord (remaining + 1)) [] [] []))) =
      some (cfg H (some (Label.oldBody MachineRegularOriginalBody.entry)) data header
        (counterStacks (encodeWord remaining) [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry)
    (some Label.ownerSeed)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_oldFuel, encodeWord, List.replicate_succ,
    List.cons_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_true, update_frame_oldFuel]
  rfl

theorem oldGuardExit (H : BaseTable) (data : Data) (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldGuard) data header (counterStacks (encodeWord 0) [] [] []))) =
      some (cfg H (some Label.ownerSeed) data header (counterStacks [] [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry)
    (some Label.ownerSeed)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_oldFuel, encodeWord, List.replicate_zero,
    List.nil_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_false, update_frame_oldFuel]
  rfl

theorem oldIncrementStep (H : BaseTable) (t : GraphTables.Table) (index : Nat)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldIncrement) (oldData t index output) header counters)) =
      some (cfg H (some .oldGuard) (oldData t (index + 1) output) header counters) := by
  change some (TM2.stepAux (Fuel.increment (coreTape 1) Label.oldGuard)
    (readyState H) (frame (oldData t index output) header counters)) = _
  simp only [Fuel.increment, TM2.stepAux, frame_core]
  change some (⟨some Label.oldGuard, readyState H,
    Function.update (frame (oldData t index output) header counters) (coreTape 1)
      (true :: encodeWord index)⟩ : TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_global]
  simp only [cfg, oldData, encodeWord, List.replicate_succ, List.cons_append]

def oldPrefix (H : BaseTable) (t : GraphTables.Table) (k : Nat) : List Bool :=
  PreprocessingRegularLoopWords.blocksPrefix (MachineRegularOriginalBody.emittedBits H t) k

noncomputable def oldElapsed (H : BaseTable) (t : GraphTables.Table) (output : List Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => oldElapsed H t output k +
      if h : k < t.darts then
        1 + MachineRegularOriginalBody.totalSteps H t ⟨k,h⟩ (output ++ oldPrefix H t k) + 1
      else 0

private theorem joinTrace_inline_MachineRegularTable {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem oldPrefixTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (k : Nat) : k ≤ t.darts →
    (advance (TM2.step (program H)))^[oldElapsed H t output k]
      (some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] []))) =
      some (cfg H (some .oldGuard) (oldData t k (output ++ oldPrefix H t k)) header
        (counterStacks (encodeWord (t.darts-k)) [] [] [])) := by
  induction k with
  | zero =>
    intro _
    simp [oldElapsed, oldPrefix]
  | succ k ih =>
    intro hk
    have hlt : k < t.darts := by omega
    have hremaining : t.darts-k = (t.darts-(k+1))+1 := by omega
    have previous := ih (by omega)
    have guard := oldGuardStep H (oldData t k (output ++ oldPrefix H t k)) header
      (t.darts-(k+1))
    rw [← hremaining] at guard
    have body := oldBodyTrace H t ⟨k,hlt⟩ (output ++ oldPrefix H t k) header
      (counterStacks (encodeWord (t.darts-(k+1))) [] [] [])
    have increment := oldIncrementStep H t k
      ((output ++ oldPrefix H t k) ++ MachineRegularOriginalBody.emittedBits H t ⟨k,hlt⟩)
      header (counterStacks (encodeWord (t.darts-(k+1))) [] [] [])
    have combined := joinTrace_inline_MachineRegularTable (joinTrace_inline_MachineRegularTable (joinTrace_inline_MachineRegularTable previous guard) body) increment
    have bits := PreprocessingRegularLoopWords.blocksPrefix_succ
      (MachineRegularOriginalBody.emittedBits H t) k hlt
    change oldPrefix H t (k+1) = oldPrefix H t k ++
      MachineRegularOriginalBody.emittedBits H t ⟨k,hlt⟩ at bits
    simpa only [oldElapsed, dite_eq_left hlt, bits, List.append_assoc, Nat.add_assoc] using combined

theorem oldLoopTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[oldElapsed H t output t.darts + 1]
      (some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] []))) =
      some (cfg H (some Label.ownerSeed)
        (oldData t t.darts (output ++ oldPrefix H t t.darts)) header
        (counterStacks [] [] [] [])) := by
  have prefixRun := oldPrefixTrace H t output header t.darts (Nat.le_refl _)
  simp only [Nat.sub_self] at prefixRun
  exact joinTrace_inline_MachineRegularTable prefixRun (oldGuardExit H _ header)

@[simp] theorem frame_scratch (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work : List Bool) :
    frame data header (counterStacks old owners dummy work) scratch = work := rfl

@[simp] theorem frame_darts (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) : frame data header counters (coreTape 6) = data.darts := rfl

@[simp] theorem frame_header_n (data : Data) (n N R : List Bool)
    (counters : Fin 4 → List Bool) :
    frame data (headerAux n N R) counters (headerTape Header.nTape) = n := rfl

theorem oldSeedStep (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldSeed) (headerData t output) header counters)) =
      some (cfg H (some (.copyFirst .old)) (oldData t 0 output) header counters) := by
  change some (TM2.stepAux (.push (coreTape 1) (fun _ => false)
    (.goto fun _ => Label.copyFirst CopyPhase.old)) (readyState H) (frame (headerData t output) header counters)) = _
  change some (⟨some (Label.copyFirst CopyPhase.old), readyState H,
    Function.update (frame (headerData t output) header counters) (coreTape 1) [false]⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_global]
  rfl

theorem copyOldTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[2*(t.darts+2)]
      (some (cfg H (some (.copyFirst .old)) (oldData t 0 output) header
        (counterStacks [] [] [] []))) =
      some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] [])) := by
  have h := MachineCopy.copyTrace (coreTape 6) oldFuel scratch
    (by decide) (by decide) (by decide) false (.copyFirst .old) (.copySecond .old)
    (some .oldGuard) (program H) rfl rfl
    (frame (oldData t 0 output) header (counterStacks [] [] [] [])) rfl
    (MachineRegularOriginalBody.readyState H) none
  simpa only [frame_darts, oldData, headerData, inputData, encodeWord_length,
    frame_oldFuel, List.append_nil, update_frame_oldFuel, cfg, readyState, Nat.add_assoc] using h

theorem oldStageTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1+2*(t.darts+2)+(oldElapsed H t output t.darts+1)]
      (some (cfg H (some .oldSeed) (headerData t output) header (counterStacks [] [] [] []))) =
      some (cfg H (some Label.ownerSeed)
        (oldData t t.darts (output ++ oldPrefix H t t.darts)) header
        (counterStacks [] [] [] [])) :=
  joinTrace_inline_MachineRegularTable (joinTrace_inline_MachineRegularTable (oldSeedStep H t output header _) (copyOldTrace H t output header))
    (oldLoopTrace H t output header)

@[simp] theorem update_frame_offset (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 5) replacement =
      frame { data with offset := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

def ownerData (t : GraphTables.Table) (index : Nat) (output : List Bool) : Data :=
  { headerData t output with
    globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset
      (PreprocessingRegularTables.padding t) index)
    owner := encodeWord index
    offset := encodeWord (PreprocessingPaddingOffsets.offset
      (PreprocessingRegularTables.padding t) index) }

theorem ownerSeedStep (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some Label.ownerSeed) (oldData t t.darts output) header counters)) =
      some (cfg H (some (.copyFirst .owner)) (ownerData t 0 output) header counters) := by
  change some (TM2.stepAux
    (.push (coreTape 2) (fun _ => false) (.push (coreTape 5) (fun _ => false)
      (.goto fun _ => Label.copyFirst CopyPhase.owner))) (readyState H)
      (frame (oldData t t.darts output) header counters)) = _
  simp only [TM2.stepAux, frame_core]
  change some (⟨some (Label.copyFirst CopyPhase.owner), readyState H,
    Function.update (Function.update (frame (oldData t t.darts output) header counters)
      (coreTape 2) [false]) (coreTape 5) [false]⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_owner, update_frame_offset]
  simp only [cfg, ownerData, oldData, PreprocessingPaddingOffsets.offset_zero, Nat.add_zero,
    encodeWord, List.replicate_zero, List.nil_append]

theorem copyOwnerTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[2*(t.vertices+2)]
      (some (cfg H (some (.copyFirst .owner)) (ownerData t 0 output) (headerStacks t)
        (counterStacks [] [] [] []))) =
      some (cfg H (some .ownerGuard) (ownerData t 0 output) (headerStacks t)
        (counterStacks [] (encodeWord t.vertices) [] [])) := by
  have h := MachineCopy.copyTrace (headerTape Header.nTape) ownerFuel scratch
    (by decide) (by decide) (by decide) false (.copyFirst .owner) (.copySecond .owner)
    (some .ownerGuard) (program H) rfl rfl
    (frame (ownerData t 0 output) (headerStacks t) (counterStacks [] [] [] [])) rfl
    (MachineRegularOriginalBody.readyState H) none
  simpa only [headerStacks, frame_header_n, encodeWord_length, frame_ownerFuel,
    List.append_nil, update_frame_ownerFuel, cfg, readyState, Nat.add_assoc] using h

theorem ownerPlacement (data extra : Data) (header : Header.Tape → List Bool)
    (old owners : List Bool) :
    MachineCloudPadding.Placement.tapes ownerView (MachineRegularOwnerBody.frame data)
      (frame extra header (counterStacks old owners [] [])) =
      frame data header (counterStacks old owners [] []) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j with
    | inl j => rfl
    | inr i => fin_cases i <;> rfl

theorem ownerInitialData_eq (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) :
    MachineRegularOwnerBody.initialData t v output = ownerData t v.val output := rfl

theorem ownerBodyTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (header : Header.Tape → List Bool) (owners : List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularOwnerBody.totalSteps H t v output]
      (some (cfg H (some (.ownerBody MachineRegularOwnerBody.entry))
        (ownerData t v.val output) header (counterStacks [] owners [] []))) =
      some (cfg H (some .ownerIncrement) (MachineRegularOwnerBody.finalData H t v output)
        header (counterStacks [] owners [] [])) := by
  have raw := MachineRegularOwnerBody.ownerTrace H t v output
  have placed := MachineCloudPadding.Placement.trace ownerTape ownerView ownerView_left ownerView_right
    Label.ownerBody (some .ownerIncrement)
    (frame (ownerData t v.val output) header (counterStacks [] owners [] []))
    (MachineRegularOwnerBody.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    ownerPlacement, MachineRegularOwnerBody.cfg, MachineRegularOwnerBody.readyState,
    ownerInitialData_eq, cfg, readyState] using placed

theorem ownerGuardStep (H : BaseTable) (data : Data) (header : Header.Tape → List Bool)
    (remaining : Nat) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerGuard) data header
        (counterStacks [] (encodeWord (remaining+1)) [] []))) =
      some (cfg H (some (.ownerBody MachineRegularOwnerBody.entry)) data header
        (counterStacks [] (encodeWord remaining) [] [])) := by
  change some (TM2.stepAux (Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry)
    (clearEntry 0)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_ownerFuel, encodeWord, List.replicate_succ,
    List.cons_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_true, update_frame_ownerFuel]
  rfl

theorem ownerGuardExit (H : BaseTable) (data : Data) (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerGuard) data header (counterStacks [] (encodeWord 0) [] []))) =
      some (cfg H (clearEntry 0) data header (counterStacks [] [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry)
    (clearEntry 0)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_ownerFuel, encodeWord, List.replicate_zero,
    List.nil_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_false, update_frame_ownerFuel]
  rfl

theorem ownerIncrementStep (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerIncrement) (MachineRegularOwnerBody.finalData H t v output)
        header counters)) =
      some (cfg H (some .ownerGuard)
        (ownerData t (v.val+1) (output ++ MachineRegularOwnerBody.ownerBits H t v)) header counters) := by
  change some (TM2.stepAux (Fuel.increment (coreTape 2) Label.ownerGuard) (readyState H)
    (frame (MachineRegularOwnerBody.finalData H t v output) header counters)) = _
  simp only [Fuel.increment, TM2.stepAux, frame_core]
  change some (⟨some Label.ownerGuard, readyState H,
    Function.update (frame (MachineRegularOwnerBody.finalData H t v output) header counters)
      (coreTape 2) (true :: encodeWord v.val)⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_owner]
  have offset := PreprocessingRegularBounds.offset_succ (PreprocessingRegularTables.padding t) v.val v.isLt
  simp only [cfg, ownerData, headerData, inputData, MachineRegularOwnerBody.finalData,
    MachineRegularOwnerBody.initialData, offset, encodeWord, List.replicate_succ,
    List.cons_append, Nat.add_assoc]

def ownerPrefix (H : BaseTable) (t : GraphTables.Table) (k : Nat) : List Bool :=
  PreprocessingRegularLoopWords.blocksPrefix (MachineRegularOwnerBody.ownerBits H t) k

noncomputable def ownerElapsed (H : BaseTable) (t : GraphTables.Table) (output : List Bool) : Nat → Nat
  | 0 => 0
  | k+1 => ownerElapsed H t output k +
      if h : k < t.vertices then
        1 + MachineRegularOwnerBody.totalSteps H t ⟨k,h⟩ (output ++ ownerPrefix H t k) + 1
      else 0

theorem ownerPrefixTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (k : Nat) : k ≤ t.vertices →
    (advance (TM2.step (program H)))^[ownerElapsed H t output k]
      (some (cfg H (some .ownerGuard) (ownerData t 0 output) header
        (counterStacks [] (encodeWord t.vertices) [] []))) =
      some (cfg H (some .ownerGuard) (ownerData t k (output ++ ownerPrefix H t k)) header
        (counterStacks [] (encodeWord (t.vertices-k)) [] [])) := by
  induction k with
  | zero =>
    intro _
    simp [ownerElapsed, ownerPrefix]
  | succ k ih =>
    intro hk
    have hlt : k < t.vertices := by omega
    have hremaining : t.vertices-k = (t.vertices-(k+1))+1 := by omega
    have previous := ih (by omega)
    have guard := ownerGuardStep H (ownerData t k (output ++ ownerPrefix H t k)) header
      (t.vertices-(k+1))
    rw [← hremaining] at guard
    have body := ownerBodyTrace H t ⟨k,hlt⟩ (output ++ ownerPrefix H t k) header
      (encodeWord (t.vertices-(k+1)))
    have increment := ownerIncrementStep H t ⟨k,hlt⟩ (output ++ ownerPrefix H t k) header
      (counterStacks [] (encodeWord (t.vertices-(k+1))) [] [])
    have combined := joinTrace_inline_MachineRegularTable (joinTrace_inline_MachineRegularTable (joinTrace_inline_MachineRegularTable previous guard) body) increment
    have bits := PreprocessingRegularLoopWords.blocksPrefix_succ
      (MachineRegularOwnerBody.ownerBits H t) k hlt
    change ownerPrefix H t (k+1) = ownerPrefix H t k ++
      MachineRegularOwnerBody.ownerBits H t ⟨k,hlt⟩ at bits
    simpa only [ownerElapsed, dite_eq_left hlt, bits, List.append_assoc, Nat.add_assoc] using combined

theorem ownerLoopTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[ownerElapsed H t output t.vertices+1]
      (some (cfg H (some .ownerGuard) (ownerData t 0 output) header
        (counterStacks [] (encodeWord t.vertices) [] []))) =
      some (cfg H (clearEntry 0)
        (ownerData t t.vertices (output ++ ownerPrefix H t t.vertices)) header
        (counterStacks [] [] [] [])) := by
  have prefixRun := ownerPrefixTrace H t output header t.vertices (Nat.le_refl _)
  simp only [Nat.sub_self] at prefixRun
  exact joinTrace_inline_MachineRegularTable prefixRun (ownerGuardExit H _ header)

theorem ownerStageTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[1+2*(t.vertices+2)+(ownerElapsed H t output t.vertices+1)]
      (some (cfg H (some Label.ownerSeed) (oldData t t.darts output) (headerStacks t)
        (counterStacks [] [] [] []))) =
      some (cfg H (clearEntry 0)
        (ownerData t t.vertices (output ++ ownerPrefix H t t.vertices)) (headerStacks t)
        (counterStacks [] [] [] [])) :=
  joinTrace_inline_MachineRegularTable (joinTrace_inline_MachineRegularTable (ownerSeedStep H t output (headerStacks t) _) (copyOwnerTrace H t output))
    (ownerLoopTrace H t output (headerStacks t))

theorem owner_output_eq_ownerPrefix (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    (Header.headerBits PreprocessingRegularTables.internalDegree t ++ oldPrefix H t t.darts) ++
        ownerPrefix H t k =
      PreprocessingRegularBounds.ownerPrefix t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) k := by
  have oldBits : MachineRegularOriginalBody.emittedBits H t =
      PreprocessingRegularWords.originalVertexBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  have ownerBits : MachineRegularOwnerBody.ownerBits H t =
      PreprocessingRegularBounds.ownerBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  simp only [Header.headerBits, Header.vertexTotal, Header.dartTotal, oldPrefix,
    ownerPrefix, PreprocessingRegularLoopWords.blocksPrefix_all,
    PreprocessingRegularBounds.ownerPrefix, PreprocessingRegularBounds.header]
  rw [oldBits, ownerBits]

def cleaned (base : Tape → List Bool) : Nat → Tape → List Bool
  | 0 => base
  | k+1 => if h : k < 7 then Function.update (cleaned base k) (clearTape ⟨k,h⟩) []
      else cleaned base k

def cleanupTime (base : Tape → List Bool) : Nat → Nat
  | 0 => 0
  | k+1 => cleanupTime base k + if h : k < 7 then
      ((cleaned base k) (clearTape ⟨k,h⟩)).length+1 else 0

theorem drainTrace (H : BaseTable) (i : Fin 7) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[(base (clearTape i)).length+1]
      (some ⟨some (.clear i), readyState H, base⟩) =
      some ⟨clearEntry (i.val+1), readyState H, Function.update base (clearTape i) []⟩ := by
  have h := MachineDrain.drainTrace (clearTape i) (.clear i) (clearEntry (i.val+1))
    (program H) rfl base (base (clearTape i)) (MachineRegularOriginalBody.readyState H) none
  simpa only [Function.update_eq_self, readyState] using h

theorem cleanupPrefixTrace (H : BaseTable) (base : Tape → List Bool) (k : Nat) (hk : k ≤ 7) :
    (advance (TM2.step (program H)))^[cleanupTime base k]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨clearEntry k, readyState H, cleaned base k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < 7 := by omega
    have first := ih (by omega)
    have second := drainTrace H ⟨k,h⟩ (cleaned base k)
    have atEntry : clearEntry k = some (.clear ⟨k,h⟩) := by simp only [clearEntry, dite_eq_left h]
    rw [atEntry] at first
    simpa only [cleanupTime, cleaned, dite_eq_left h] using joinTrace_inline_MachineRegularTable first second

theorem cleanupTrace (H : BaseTable) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[cleanupTime base 7]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨none, readyState H, cleaned base 7⟩ := by
  simpa only [clearEntry, lt_self_iff_false, dite_false] using cleanupPrefixTrace H base 7 le_rfl

def finalStacks (t : GraphTables.Table) (output : List Bool) : Tape → List Bool :=
  frame (ownerData t t.vertices output) (headerStacks t) (counterStacks [] [] [] [])

theorem cleaned_finalStacks (t : GraphTables.Table) (output : List Bool) :
    cleaned (finalStacks t output) 7 =
      frame (inputData t output) (fun _ => []) (counterStacks [] [] [] []) := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j with
    | inl k => cases k with
      | inl k => cases k with
        | inner k => cases k <;> rfl
        | bound => rfl
        | remaining => rfl
        | total => rfl
      | inr k => cases k <;> rfl
    | inr i => fin_cases i <;> rfl

theorem cleaned_length_le (base : Tape → List Bool) (k : Nat) :
    ∀ j, (cleaned base k j).length ≤ (base j).length := by
  induction k with
  | zero => intro j; exact Nat.le_refl _
  | succ k ih =>
    intro j
    simp only [cleaned]
    split
    · rename_i hk
      by_cases hj : j = clearTape ⟨k,hk⟩
      · simp [hj]
      · simpa only [Function.update_of_ne hj] using ih j
    · exact ih j

theorem cleanupTime_le (base : Tape → List Bool) (cap : Nat)
    (bounded : ∀ i : Fin 7, (base (clearTape i)).length ≤ cap) (k : Nat) :
    cleanupTime base k ≤ k*(cap+1) := by
  induction k with
  | zero => simp [cleanupTime]
  | succ k ih =>
    simp only [cleanupTime]
    split
    · rename_i hk
      have hword := (cleaned_length_le base k (clearTape ⟨k,hk⟩)).trans (bounded ⟨k,hk⟩)
      calc
        cleanupTime base k + ((cleaned base k (clearTape ⟨k,hk⟩)).length+1) ≤
            k*(cap+1)+(cap+1) := by omega
        _ = (k+1)*(cap+1) := by simp only [Nat.add_mul, one_mul]
    · exact ih.trans (Nat.mul_le_mul_right _ (by omega))

theorem cleanupTime_final_le (t : GraphTables.Table) (output : List Bool) :
    cleanupTime (finalStacks t output) 7 ≤
      (7*(ExpanderFamily.growth*(PreprocessingRegularTables.internalDegree+4)+4)) *
        (PreprocessingMachineBounds.inputLength t+1) := by
  let L := PreprocessingMachineBounds.inputLength t
  let g := ExpanderFamily.growth
  let q := PreprocessingRegularTables.internalDegree
  let C := g*(q+4)+4
  have hm : t.darts ≤ L := GraphTables.darts_le_tableBits_length t
  have hn : t.vertices ≤ L := GraphTables.vertices_le_tableBits_length t
  have hs : PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices ≤ g*L :=
    PreprocessingMachineBounds.prefix_le_input t t.vertices
  have hN : Header.vertexTotal t ≤ g*L := PreprocessingMachineBounds.regularVertices_le_input t
  have hone : 1 ≤ C := by dsimp [C]; omega
  have hg : g ≤ C := by
    have h := Nat.mul_le_mul_left g (show 1 ≤ q+4 by omega)
    dsimp [C]
    omega
  have hgp : g+1 ≤ C := by
    have h := Nat.mul_le_mul_left g (show 1 ≤ q+4 by omega)
    dsimp [C]
    omega
  have hgq : g*(q+1) ≤ C := by
    have h := Nat.mul_le_mul_left g (show q+1 ≤ q+4 by omega)
    dsimp [C]
    omega
  have hmC : t.darts ≤ C*L := hm.trans (by simpa using Nat.mul_le_mul_right L hone)
  have hnC : t.vertices ≤ C*L := hn.trans (by simpa using Nat.mul_le_mul_right L hone)
  have hsC : PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices ≤ C*L :=
    hs.trans (Nat.mul_le_mul_right L hg)
  have hNC : Header.vertexTotal t ≤ C*L := hN.trans (Nat.mul_le_mul_right L hg)
  have hxC : t.darts +
      PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices ≤ C*L := by
    calc
      _ ≤ L+g*L := Nat.add_le_add hm hs
      _ = (g+1)*L := by simp only [Nat.add_mul, one_mul, Nat.add_comm]
      _ ≤ C*L := Nat.mul_le_mul_right L hgp
  have hRC : Header.dartTotal q t ≤ C*L := by
    calc
      _ ≤ (g*L)*(q+1) := Nat.mul_le_mul_right _ hN
      _ = (g*(q+1))*L := by ac_rfl
      _ ≤ C*L := Nat.mul_le_mul_right L hgq
  have bounds : ∀ i : Fin 7, (finalStacks t output (clearTape i)).length ≤ C*L+1 := by
    intro i
    fin_cases i
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hxC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hnC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hsC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hmC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hnC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hNC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hRC 1
  have actual := cleanupTime_le (finalStacks t output) (C*L+1) bounds 7
  have hC : 2 ≤ C := by dsimp [C]; omega
  change cleanupTime (finalStacks t output) 7 ≤ (7*C)*(L+1)
  nlinarith

def headerOutput (t : GraphTables.Table) : List Bool :=
  Header.headerBits PreprocessingRegularTables.internalDegree t

def oldOutput (H : BaseTable) (t : GraphTables.Table) : List Bool :=
  headerOutput t ++ oldPrefix H t t.darts

def finalOutput (H : BaseTable) (t : GraphTables.Table) : List Bool :=
  oldOutput H t ++ ownerPrefix H t t.vertices

noncomputable def totalTime (H : BaseTable) (t : GraphTables.Table) : Nat :=
  Header.totalTime PreprocessingRegularTables.internalDegree t [] +
    (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1)) +
    (1+2*(t.vertices+2)+(ownerElapsed H t (oldOutput H t) t.vertices+1)) +
    cleanupTime (finalStacks t (finalOutput H t)) 7

theorem old_output_eq_originalPrefix (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    Header.headerBits PreprocessingRegularTables.internalDegree t ++ oldPrefix H t k =
      PreprocessingRegularBounds.originalPrefix t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) k := rfl

theorem finalOutput_eq (H : BaseTable) (t : GraphTables.Table) :
    finalOutput H t = PortTables.tableBits (PreprocessingRegularTables.regularize H t) := by
  change finalOutput H t = PortTables.tableBits (PreprocessingRegularTables.ofCloudTables t
    (PreprocessingRegularTables.padding t) (PreprocessingRegularTables.familyCloudTable H t))
  rw [PreprocessingRegularWords.tableBits_ofCloudTables]
  have oldBits : MachineRegularOriginalBody.emittedBits H t =
      PreprocessingRegularWords.originalVertexBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  have ownerBits : MachineRegularOwnerBody.ownerBits H t =
      (fun v => (List.ofFn (PreprocessingRegularWords.dummyVertexBits t
        (PreprocessingRegularTables.padding t) (PreprocessingRegularTables.familyCloudTable H t) v)).flatten) := rfl
  simp only [finalOutput, oldOutput, headerOutput, Header.headerBits, Header.vertexTotal,
    Header.dartTotal, oldPrefix, ownerPrefix, PreprocessingRegularLoopWords.blocksPrefix_all,
    List.append_assoc]
  rw [oldBits, ownerBits]

end Top

end DFVSGames.Foundations.Complexity.MachineRegularTable
end

section

namespace DFVSGames.Foundations.Complexity.MachineRegularTable.Top

open Turing MachineComposition
open DFVSGames.Foundations.PCP

private theorem joinTraceRegularTableTrace_inline_MachineRegularTableTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

private theorem normalizeEmptyAppend_inline_MachineRegularTableTrace {A : Type*} (output : List Bool → A)
    (bits : List Bool) : output ([] ++ bits) = output bits :=
  congrArg output (List.nil_append bits)

theorem headerStartTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[Header.totalTime PreprocessingRegularTables.internalDegree t []]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H (some .oldSeed) (headerData t (headerOutput t)) (headerStacks t)
        (counterStacks [] [] [] [])) := by
  have run := headerTrace H t [] (counterStacks [] [] [] [])
  exact run.trans (normalizeEmptyAppend_inline_MachineRegularTableTrace
    (fun output : List Bool => some (cfg H (some Label.oldSeed)
      (headerData t output) (headerStacks t) (counterStacks [] [] [] [])))
    (Header.headerBits PreprocessingRegularTables.internalDegree t))

theorem headerOldTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[
      Header.totalTime PreprocessingRegularTables.internalDegree t [] +
        (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1))]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H (some .ownerSeed) (oldData t t.darts (oldOutput H t)) (headerStacks t)
        (counterStacks [] [] [] [])) := by
  have first := headerStartTrace H t
  have second := oldStageTrace H t (headerOutput t) (headerStacks t)
  have joined := joinTraceRegularTableTrace_inline_MachineRegularTableTrace (f := advance (TM2.step (program H))) first second
  have output_eq : headerOutput t ++ oldPrefix H t t.darts = oldOutput H t := rfl
  exact joined.trans (congrArg
    (fun output : List Bool => some (cfg H (some Label.ownerSeed)
      (oldData t t.darts output) (headerStacks t) (counterStacks [] [] [] []))) output_eq)

theorem beforeCleanupTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[
      Header.totalTime PreprocessingRegularTables.internalDegree t [] +
        (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1)) +
        (1+2*(t.vertices+2)+(ownerElapsed H t (oldOutput H t) t.vertices+1))]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some ⟨clearEntry 0, readyState H, finalStacks t (finalOutput H t)⟩ := by
  have first := headerOldTrace H t
  have second := ownerStageTrace H t (oldOutput H t)
  have joined := joinTraceRegularTableTrace_inline_MachineRegularTableTrace (f := advance (TM2.step (program H))) first second
  have output_eq : oldOutput H t ++ ownerPrefix H t t.vertices = finalOutput H t := rfl
  exact joined.trans (congrArg
    (fun output : List Bool => some (cfg H (clearEntry 0)
      (ownerData t t.vertices output) (headerStacks t) (counterStacks [] [] [] []))) output_eq)

theorem cleanupFinalTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[cleanupTime (finalStacks t output) 7]
      (some ⟨clearEntry 0, readyState H, finalStacks t output⟩) =
      some (cfg H none (inputData t output) (fun _ => []) (counterStacks [] [] [] [])) :=
  (cleanupTrace H (finalStacks t output)).trans
    (congrArg (fun terminalStacks => some (⟨none, readyState H, terminalStacks⟩ : TM2.Cfg Alphabet Label State))
      (cleaned_finalStacks t output))

theorem fullTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[totalTime H t]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H none (inputData t (finalOutput H t)) (fun _ => [])
        (counterStacks [] [] [] [])) :=
  joinTraceRegularTableTrace_inline_MachineRegularTableTrace (f := advance (TM2.step (program H))) (beforeCleanupTrace H t) (cleanupFinalTrace H t (finalOutput H t))

@[simp] theorem update_frame_output (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 8) replacement =
      frame { data with output := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

theorem input_stacks_eq (H : BaseTable) (t : GraphTables.Table) :
    frame (inputData t []) (fun _ => []) (counterStacks [] [] [] []) =
      (Turing.initList (machine H) (GraphTables.tableBits t)).stk := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i =>
        fin_cases i <;>
        simp [Turing.initList, machine, coreTape, frame, inputData,
          MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
        rfl
    | inr e => cases e with
      | inl e => cases e <;>
          simp [Turing.initList, machine, coreTape, frame, inputData,
            MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      | inr e =>
          simp [Turing.initList, machine, coreTape, frame,
            MachineRegularOriginalBody.frame]
  | inr j => cases j with
    | inl j => simp [Turing.initList, machine, coreTape, frame]
    | inr j => fin_cases j <;> simp [Turing.initList, machine, coreTape, frame, counterStacks]

theorem initial_cfg_eq (H : BaseTable) (t : GraphTables.Table) :
    cfg H (some (.header .init)) (inputData t []) (fun _ => []) (counterStacks [] [] [] []) =
      Turing.initList (machine H) (GraphTables.tableBits t) := by
  change (⟨some (.header .init), readyState H,
    frame (inputData t []) (fun _ => []) (counterStacks [] [] [] [])⟩ : TM2.Cfg Alphabet Label State) =
    ⟨some (.header .init), readyState H, (Turing.initList (machine H) (GraphTables.tableBits t)).stk⟩
  rw [input_stacks_eq]

theorem trace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[totalTime H t]
      (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
      some ⟨none, readyState H,
        Function.update (Turing.initList (machine H) (GraphTables.tableBits t)).stk
          (coreTape 8) (PortTables.tableBits (PreprocessingRegularTables.regularize H t))⟩ := by
  have full := fullTrace H t
  rw [initial_cfg_eq, finalOutput_eq] at full
  have final_stacks :
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
          (fun _ => []) (counterStacks [] [] [] []) =
        Function.update (Turing.initList (machine H) (GraphTables.tableBits t)).stk (coreTape 8)
          (PortTables.tableBits (PreprocessingRegularTables.regularize H t)) := by
    rw [← input_stacks_eq]
    exact (update_frame_output (inputData t []) (fun _ => []) (counterStacks [] [] [] [])
      (PortTables.tableBits (PreprocessingRegularTables.regularize H t))).symm
  change (advance (TM2.step (program H)))^[totalTime H t]
    (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
    some ⟨none, readyState H,
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
        (fun _ => []) (counterStacks [] [] [] [])⟩ at full
  rw [final_stacks] at full
  exact full

end DFVSGames.Foundations.Complexity.MachineRegularTable.Top
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
