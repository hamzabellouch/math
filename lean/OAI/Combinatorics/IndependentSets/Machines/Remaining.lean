import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.Tape2

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineOverlayTable
open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingOverlayWords
open MachineCloudPadding

variable {A : Type}

def remaining {n : Nat} (block : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn block).drop k).flatten
def emittedPrefix {n : Nat} (block : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn block).take k).flatten

theorem remaining_step {n : Nat} (block : Fin n → List Bool) (v : Fin n) :
    remaining block v.val = block v ++ remaining block (v.val + 1) := by
  have hs := List.getElem_cons_drop (as := List.ofFn block) (i := v.val)
    (by simpa only [List.length_ofFn] using v.isLt)
  unfold remaining
  rw [← hs]
  simp only [List.flatten_cons, List.getElem_ofFn, Fin.eta]

theorem prefix_step {n : Nat} (block : Fin n → List Bool) (v : Fin n) :
    emittedPrefix block (v.val + 1) = emittedPrefix block v.val ++ block v := by
  unfold emittedPrefix
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using v.isLt)]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.getElem_ofFn, Fin.eta]

@[simp] theorem remaining_zero {n : Nat} (block : Fin n → List Bool) :
    remaining block 0 = (List.ofFn block).flatten := by simp [remaining]
@[simp] theorem remaining_end {n : Nat} (block : Fin n → List Bool) :
    remaining block n = [] := by
  unfold remaining
  rw [List.drop_eq_nil_iff.mpr (by simpa only [List.length_ofFn] using (Nat.le_refl n)), List.flatten_nil]
@[simp] theorem prefix_zero {n : Nat} (block : Fin n → List Bool) : emittedPrefix block 0 = [] := by
  simp [emittedPrefix]
@[simp] theorem prefix_end {n : Nat} (block : Fin n → List Bool) :
    emittedPrefix block n = (List.ofFn block).flatten := by
  unfold emittedPrefix
  have ht : (List.ofFn block).take n = List.ofFn block :=
    List.take_of_length_le (by simpa only [List.length_ofFn] using (Nat.le_refl n))
  rw [ht]

theorem oldFrame {n m : Nat} (g h gs hs nv mv f v out : List Bool)
    (rows : List (DartRow n m)) :
    MachineLazyRows.streamFrame oldTapes (memory g h gs hs nv mv f v [] []) rows out =
      memory g h (MachineLazyRows.recordsInput rows ++ gs) hs nv mv f v [] out := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [MachineLazyRows.streamFrame, oldTapes, memory, tail, oldReverse, relation,
      scratch, dividedCopy, quotient, newReverse, output, rowBuffer, graphStream]

theorem expanderFrame (g h gs hs nv mv f v t out : List Bool) (words : List Nat) :
    MachineOverlayRows.streamFrame expanderTapes (memory g h gs hs nv mv f v t []) words out =
      memory g h gs (encodeWords words ++ hs) nv mv f v t out := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [MachineOverlayRows.streamFrame, expanderTapes, memory, tail, oldReverse,
      relation, scratch, dividedCopy, quotient, newReverse, output, rowBuffer, expanderStream]

theorem oldVertexTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (v : Fin n) (g h gs hs nv mv f current out : List Bool) (a : A) :
    (advance (TM2.step (program d e hd he)))^[MachineLazyRows.vertexSteps d (d + e) 0 (oldRows G v) out]
      (some ⟨next (.old (0, none)), clean d e hd he a,
        memory g h (oldBlock G v ++ gs) hs nv mv f current [] out⟩) =
      some ⟨next .tailSeed, clean d e hd he a,
        memory g h gs hs nv mv f current [] (out ++ oldOutput G e v)⟩ := by
  have hrun := MachineLazyRows.vertexTrace d hd (d + e) 0 oldTapes oldTapes_injective
    (fun stage => .inr (.old stage)) (next .tailSeed) (program d e hd he) (fun _ => rfl)
    (memory g h gs hs nv mv f current [] []) (row G v)
    (by
      intro i hi7 hi9
      fin_cases i <;> simp_all [oldTapes, memory, tail, oldReverse, relation, scratch,
        dividedCopy, quotient, newReverse, output, rowBuffer, graphStream])
    (a, MachineFixedDivMod.residue e he 0) out
  simpa only [next, oldFrame, MachineLazyRows.recordsInput, List.flatMap_nil, List.nil_append,
    clean, oldBlock, oldRows, oldOutput] using hrun

theorem expanderVertexTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (H : ExpanderTables.Table n e) (v : Fin n) (g h gs hs nv mv f current out : List Bool) (a : A) :
    (advance (TM2.step (program d e hd he)))^[MachineOverlayRows.vertexSteps d e v.val
      (List.ofFn (expanderValues H v)) out]
      (some ⟨next (.expander (0, none)), clean d e hd he a,
        memory g h gs (expanderBlock H v ++ hs) nv mv f current (encodeWord v.val) out⟩) =
      some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f current (encodeWord v.val) (out ++ expanderOutput d H v)⟩ := by
  let source := MachineStateEquiv.program (expanderState A d e).symm (program d e hd he)
  have code (stage : MachineOverlayRows.VertexLabel e) : source (.inr (.expander stage)) =
      MachineOverlayRows.vertexInstruction d e he expanderTapes
        (fun stage => .inr (.expander stage)) (next .drainTail) stage := by
    change MachineStateEquiv.statement (expanderState A d e).symm
      (MachineStateEquiv.statement (expanderState A d e) _) = _
    exact MachineStateEquiv.statement_symm_statement _ _
  have native := MachineOverlayRows.vertexTrace d e he expanderTapes expanderTapes_injective
    (fun stage => .inr (.expander stage)) (next .drainTail) source code
    (memory g h gs hs nv mv f current (encodeWord v.val) []) v.val (expanderValues H v)
    rfl
    (by
      intro i hi0 hi7 hi9
      fin_cases i <;> simp_all [expanderTapes, memory, tail, oldReverse, relation, scratch,
        dividedCopy, quotient, newReverse, output, rowBuffer, expanderStream])
    ((a, MachineRegularOriginalRow.zeroBuffer), MachineFixedDivMod.residue d hd 0) out
  have transported := MachineStateEquiv.trace (expanderState A d e) source _ _ _ native
  have back : MachineStateEquiv.program (expanderState A d e) source = program d e hd he :=
    MachineStateEquiv.program_symm_program (expanderState A d e).symm _
  rw [back] at transported
  simpa only [next, MachineStateEquiv.configuration, expanderState_clean, expanderFrame,
    encodeWords, List.nil_append, expanderBlock, expanderOutput] using transported

theorem tailCopyTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs hs nv mv f out : List Bool) (k : Nat) (a : A) :
    (advance (TM2.step (program d e hd he)))^[2 * (k + 1) + 1]
      (some ⟨next .tailSeed, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩) =
      some ⟨next (.expander (0, none)), clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩ := by
  let ambient := (clean d e hd he a).1
  have hrun := MachineUnaryAffineAt.seededAffineTrace vertex scratch tail
    (by decide) (by decide) (by decide) 1 0
    (.inr .tailSeed) (.inr .tailScan) (.inr .tailRestore) (next (.expander (0, none)))
    (program d e hd he) rfl rfl rfl
    (memory g h gs hs nv mv f (encodeWord k) [] out) k []
    (by simp [memory, vertex]) rfl ambient none
  simpa only [memory_tail, next, List.append_nil, Nat.one_mul, Nat.add_zero, update_tail,
    ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hrun

theorem tailFinishTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs hs nv mv f out : List Bool) (k : Nat) (a : A) :
    (advance (TM2.step (program d e hd he)))^[k + 3]
      (some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (k + 1)) [] out⟩ := by
  let ambient := (clean d e hd he a).1
  have hd₀ := MachineDrain.drainTrace tail (.inr .drainTail) (next .increment)
    (program d e hd he) rfl (memory g h gs hs nv mv f (encodeWord k) [] out)
    (encodeWord k) ambient none
  have drain : (advance (TM2.step (program d e hd he)))^[k + 2]
      (some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩) =
      some ⟨next .increment, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩ := by
    simpa only [next, encodeWord_length, Nat.add_assoc, update_tail, ambient, clean,
      MachineLazyRows.streamClean, MachinePortReindex.clean] using hd₀
  have increment : (advance (TM2.step (program d e hd he)))^[1]
      (some ⟨next .increment, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (k + 1)) [] out⟩ := by
    change some (TM2.stepAux (program d e hd he (.inr .increment)) _ _) = _
    simp only [program, mainInstruction, TM2.stepAux, memory_vertex, next,
      update_vertex, encodeWord, List.replicate_succ, List.cons_append]
  have all := joinTrace drain increment
  simpa only [Nat.add_assoc] using all

def pairSteps {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) (out : List Bool) : Nat :=
  MachineLazyRows.vertexSteps d (d + e) 0 (oldRows G v) out + (2 * (v.val + 1) + 1) +
    MachineOverlayRows.vertexSteps d e v.val (List.ofFn (expanderValues H v))
      (out ++ oldOutput G e v) + (v.val + 3)

theorem pairTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (v : Fin n)
    (g h gs hs nv mv f out : List Bool) (a : A) :
    (advance (TM2.step (program d e hd he)))^[pairSteps G H v out]
      (some ⟨next (.old (0, none)), clean d e hd he a,
        memory g h (oldBlock G v ++ gs) (expanderBlock H v ++ hs)
          nv mv f (encodeWord v.val) [] out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (v.val + 1)) [] (out ++ outputBlock G H v)⟩ := by
  have h₁ := oldVertexTrace d e hd he G v g h gs (expanderBlock H v ++ hs)
    nv mv f (encodeWord v.val) out a
  have h₂ := tailCopyTrace d e hd he g h gs (expanderBlock H v ++ hs)
    nv mv f (out ++ oldOutput G e v) v.val a
  have h₃ := expanderVertexTrace d e hd he H v g h gs hs nv mv f
    (encodeWord v.val) (out ++ oldOutput G e v) a
  have h₄ := tailFinishTrace d e hd he g h gs hs nv mv f
    ((out ++ oldOutput G e v) ++ expanderOutput d H v) v.val a
  simpa only [pairSteps, outputBlock, List.append_assoc] using
    joinTrace (joinTrace (joinTrace h₁ h₂) h₃) h₄

def cleanupSteps (n m : Nat) : Nat := 2 * n + m + 8

theorem cleanupTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h out : List Bool) (n m : Nat) (a : A) :
    (advance (TM2.step (program d e hd he)))^[cleanupSteps n m]
      (some ⟨next .drainFuel, clean d e hd he a,
        memory g h [] [] (encodeWord n) (encodeWord m) (encodeWord 0) (encodeWord n) [] out⟩) =
      some ⟨none, clean d e hd he a, memory g h [] [] [] [] [] [] [] out⟩ := by
  let ambient := (clean d e hd he a).1
  have h₁ := MachineDrain.drainTrace fuel (.inr .drainFuel) (next .drainVertex)
    (program d e hd he) rfl
    (memory g h [] [] (encodeWord n) (encodeWord m) [] (encodeWord n) [] out)
    (encodeWord 0) ambient none
  have h₂ := MachineDrain.drainTrace vertex (.inr .drainVertex) (next .drainVertexCount)
    (program d e hd he) rfl
    (memory g h [] [] (encodeWord n) (encodeWord m) [] [] [] out)
    (encodeWord n) ambient none
  have h₃ := MachineDrain.drainTrace vertexCount (.inr .drainVertexCount) (next .drainDartCount)
    (program d e hd he) rfl (memory g h [] [] [] (encodeWord m) [] [] [] out)
    (encodeWord n) ambient none
  have h₄ := MachineDrain.drainTrace dartCount (.inr .drainDartCount) none
    (program d e hd he) rfl (memory g h [] [] [] [] [] [] [] out)
    (encodeWord m) ambient none
  simp only [encodeWord_length, update_fuel, update_vertex, update_vertexCount, update_dartCount] at h₁ h₂ h₃ h₄
  have all := joinTrace (joinTrace (joinTrace h₁ h₂) h₃) h₄
  have hsteps : cleanupSteps n m = ((0 + 1 + 1 + (n + 1 + 1)) + (n + 1 + 1)) + (m + 1 + 1) := by
    unfold cleanupSteps
    omega
  rw [hsteps]
  exact all

def rawExpander {n e : Nat} (H : ExpanderTables.Table n e) : List Bool :=
  encodeWords (ExpanderTableWords.rotationWords H)

def outputPrefix {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (k : Nat) : List Bool := encodeWords [n, n * (d + e)] ++ emittedPrefix (outputBlock G H) k

theorem outputPrefix_step {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) :
    outputPrefix G H (v.val + 1) = outputPrefix G H v.val ++ outputBlock G H v := by
  simp only [outputPrefix, prefix_step, List.append_assoc]

def loopBase {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (r : Nat) : Tape → List Bool :=
  memory (PortTables.tableBits G) (rawExpander H)
    (remaining (oldBlock G) (n - r)) (remaining (expanderBlock H) (n - r))
    (encodeWord n) (encodeWord (n * d)) [] (encodeWord (n - r)) [] (outputPrefix G H (n - r))

def loopCost {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (r : Nat) : Nat :=
  if hr : r < n then
    pairSteps G H ⟨n - (r + 1), by omega⟩ (outputPrefix G H (n - (r + 1)))
  else 0

theorem loopBodyTraces {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : A) :
    MachineCountedLoop.BodyTraces fuel (.inr .guard) (.inr (.old (0, none)))
      (program d e hd he) [] (fun _ => (clean d e hd he a).1) (fun _ => none)
      (loopBase G H) (loopCost G H) n := by
  intro r hr
  let v : Fin n := ⟨n - (r + 1), by omega⟩
  have hv : v.val + 1 = n - r := by dsimp [v]; omega
  have hinput : MachineUnaryCounter.counterTapes fuel (loopBase G H (r + 1)) r [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (oldBlock G v ++ remaining (oldBlock G) (v.val + 1))
        (expanderBlock H v ++ remaining (expanderBlock H) (v.val + 1))
        (encodeWord n) (encodeWord (n * d)) (encodeWord r) (encodeWord v.val) []
        (outputPrefix G H v.val) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel]
    change memory _ _ (remaining (oldBlock G) v.val) (remaining (expanderBlock H) v.val)
      _ _ _ _ _ _ = _
    rw [remaining_step (oldBlock G) v, remaining_step (expanderBlock H) v]
  have houtput : MachineUnaryCounter.counterTapes fuel (loopBase G H r) r [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (remaining (oldBlock G) (v.val + 1)) (remaining (expanderBlock H) (v.val + 1))
        (encodeWord n) (encodeWord (n * d)) (encodeWord r) (encodeWord (v.val + 1)) []
        (outputPrefix G H v.val ++ outputBlock G H v) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel]
    rw [← hv, outputPrefix_step]
  have run := pairTrace d e hd he G H v (PortTables.tableBits G) (rawExpander H)
    (remaining (oldBlock G) (v.val + 1)) (remaining (expanderBlock H) (v.val + 1))
    (encodeWord n) (encodeWord (n * d)) (encodeWord r) (outputPrefix G H v.val) a
  change (advance (TM2.step (program d e hd he)))^[loopCost G H r]
    (some ⟨next (.old (0, none)), clean d e hd he a,
      MachineUnaryCounter.counterTapes fuel (loopBase G H (r + 1)) r []⟩) =
    some ⟨next .guard, clean d e hd he a,
      MachineUnaryCounter.counterTapes fuel (loopBase G H r) r []⟩
  rw [hinput, houtput]
  simpa only [loopCost, dite_eq_left hr, v] using run

theorem loopTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : A) :
    (advance (TM2.step (program d e hd he)))^[MachineCountedLoop.totalSteps (loopCost G H) n]
      (some ⟨next .guard, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H)
          (MachineTableSplit.rowsBits (PortTables.graphTable G)) (rawExpander H)
          (encodeWord n) (encodeWord (n * d)) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩) =
      some ⟨next .drainFuel, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] []
          (encodeWord n) (encodeWord (n * d)) (encodeWord 0) (encodeWord n) []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩ := by
  have run := MachineCountedLoop.loopTrace fuel (.inr .guard) (.inr (.old (0, none)))
    (.inr .drainFuel) (program d e hd he) rfl []
    (fun _ => (clean d e hd he a).1) (fun _ => none) (loopBase G H) (loopCost G H) n
    (loopBodyTraces d e hd he G H a)
  have startFrame : MachineUnaryCounter.counterTapes fuel (loopBase G H n) n [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (MachineTableSplit.rowsBits (PortTables.graphTable G)) (rawExpander H)
        (encodeWord n) (encodeWord (n * d)) (encodeWord n) (encodeWord 0) []
        (encodeWords [n, n * (d + e)]) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel,
      Nat.sub_self, remaining_zero, outputPrefix, prefix_zero]
    simp only [graphRows_blocks, rawExpander, expanderRows_blocks]
  have endFrame : MachineUnaryCounter.counterTapes fuel (loopBase G H 0) 0 [] =
      memory (PortTables.tableBits G) (rawExpander H) [] []
        (encodeWord n) (encodeWord (n * d)) (encodeWord 0) (encodeWord n) []
        (PortTables.tableBits (PreprocessingOverlayTables.overlay G H)) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel,
      Nat.sub_zero, remaining_end, outputPrefix, prefix_end, tableBits_blocks]
  simp only [MachineCountedLoop.guardConfiguration, MachineCountedLoop.exitConfiguration] at run
  rw [startFrame, endFrame] at run
  simpa only [next, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using run

def tableSteps {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) : Nat :=
  MachineTableSplit.exactSteps n (n * d) (MachineTableSplit.rowsBits (PortTables.graphTable G)) +
    preparationSteps n (rawExpander H) + MachineCountedLoop.totalSteps (loopCost G H) n +
    cleanupSteps n (n * d)

theorem tableTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : A) :
    (advance (TM2.step (program d e hd he)))^[tableSteps G H]
      (some ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (PortTables.tableBits G) (rawExpander H)⟩) =
      some ⟨none, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] [] [] [] [] [] []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩ := by
  have h₁ := splitTrace d e hd he (PortTables.graphTable G) (rawExpander H) a
  rw [splitTapes_memory] at h₁
  have header : encodeWords [n, n * d] ++ MachineTableSplit.rowsBits (PortTables.graphTable G) =
      PortTables.tableBits G := (MachineTableSplit.tableBits_header_rows (PortTables.graphTable G)).symm
  change (advance (TM2.step (program d e hd he)))^[MachineTableSplit.exactSteps n (n * d)
      (MachineTableSplit.rowsBits (PortTables.graphTable G))]
    (some ⟨some (.inl .copyFirst), clean d e hd he a,
      initialTapes (PortTables.tableBits G) (rawExpander H)⟩) =
    some ⟨next .copyHFirst, clean d e hd he a,
      memory (encodeWords [n, n * d] ++ MachineTableSplit.rowsBits (PortTables.graphTable G))
        (rawExpander H) (MachineTableSplit.rowsBits (PortTables.graphTable G)) []
        (encodeWord n) (encodeWord (n * d)) [] [] [] []⟩ at h₁
  rw [header] at h₁
  have h₂ := preparationTrace d e hd he (PortTables.tableBits G) (rawExpander H)
    (MachineTableSplit.rowsBits (PortTables.graphTable G)) n (n * d) a
  have h₃ := loopTrace d e hd he G H a
  have h₄ := cleanupTrace d e hd he (PortTables.tableBits G) (rawExpander H)
    (PortTables.tableBits (PreprocessingOverlayTables.overlay G H)) n (n * d) a
  exact joinTrace (joinTrace (joinTrace h₁ h₂) h₃) h₄

private theorem flatMap_length_le {α : Type*} (items : List α) (f : α → List Bool)
    (B : Nat) (bounded : ∀ x ∈ items, (f x).length ≤ B) :
    (items.flatMap f).length ≤ items.length * B := by
  induction items with
  | nil => simp
  | cons x xs ih =>
      have hx := bounded x (by simp)
      have ht := ih (fun y hy => bounded y (by simp [hy]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

private theorem flatten_length_le (items : List (List Bool)) (B : Nat)
    (bounded : ∀ x ∈ items, x.length ≤ B) : items.flatten.length ≤ items.length * B := by
  simpa only [List.flatMap_id] using flatMap_length_le items id B bounded

def oldSize (d e n : Nat) : Nat := MachineLazyRows.rowSizeBound (d + e) 0 n (n * d)
def expanderSize (d e n : Nat) : Nat := MachineOverlayRows.rowSizeBound d e n (n * e)
def blockSize (d e n : Nat) : Nat := d * oldSize d e n + e * expanderSize d e n

theorem oldOutput_length_le {n d : Nat} (G : PortTables.Table n d) (e : Nat) (v : Fin n) :
    (oldOutput G e v).length ≤ d * oldSize d e n := by
  have bound := flatMap_length_le (oldRows G v)
    (fun r => MachineLazyRows.reindexRowBits d (d + e) 0 r.tail.val r.reverseIndex.val r.relation)
    (oldSize d e n) (fun r _ => MachineLazyRows.reindexRowBits_length_le d (d + e) 0 r)
  simpa only [oldOutput, MachineLazyRows.recordsOutput, oldRows, List.length_ofFn] using bound

theorem expanderOutput_length_le {n e : Nat} (d : Nat) (H : ExpanderTables.Table n e)
    (v : Fin n) : (expanderOutput d H v).length ≤ e * expanderSize d e n := by
  have bound := flatMap_length_le (List.ofFn (expanderValues H v))
    (MachineOverlayRows.rowBits d e v.val) (expanderSize d e n) (by
      intro j hj
      obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hj
      have hrow := MachineOverlayRows.rowBits_length_le d e v.val (expanderValues H v p)
        (n * e) (MachineOverlayRows.expanderValues_bounded H v p)
      have hv := v.isLt.le
      unfold expanderSize MachineOverlayRows.rowSizeBound at *
      omega)
  simpa only [expanderOutput, MachineOverlayRows.streamOutput, List.length_ofFn] using bound

theorem outputBlock_length_le {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) :
    (outputBlock G H v).length ≤ blockSize d e n := by
  have hg := oldOutput_length_le G e v
  have hh := expanderOutput_length_le d H v
  simp only [outputBlock, List.length_append, blockSize]
  omega

def outputCapacity (d e n : Nat) : Nat := n + n * (d + e) + 2 + n * blockSize d e n

theorem outputPrefix_length_le {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (k : Nat) :
    (outputPrefix G H k).length ≤ outputCapacity d e n := by
  have hblocks := flatten_length_le ((List.ofFn (outputBlock G H)).take k)
    (blockSize d e n) (by
      intro xs hx
      have hm := List.mem_of_mem_take hx
      obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hm
      exact outputBlock_length_le G H v)
  have hlen : ((List.ofFn (outputBlock G H)).take k).length ≤ n := by
    simp only [List.length_take, List.length_ofFn]
    exact Nat.min_le_right _ _
  have hcap := Nat.mul_le_mul_right (blockSize d e n) hlen
  simp only [outputPrefix, emittedPrefix, List.length_append, encodeWords_length,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, Nat.add_zero, outputCapacity]
  omega

def pairBudget (d e n : Nat) : Nat :=
  (d * (MachineLazyRows.rowCostBound (d + e) 0 n (n * d) +
    2 * (outputCapacity d e n + d * oldSize d e n) + 1) + 1) +
  (e * (MachineOverlayRows.rowCostBound d e n (n * e) +
    2 * (outputCapacity d e n + d * oldSize d e n + e * expanderSize d e n) + 1) + 1) +
  (3 * n + 6)

theorem pairSteps_le {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (out : List Bool)
    (hout : out.length ≤ outputCapacity d e n) : pairSteps G H v out ≤ pairBudget d e n := by
  have hold := MachineLazyRows.vertexSteps_le d (d + e) 0 (oldRows G v) out
  simp only [oldRows, List.length_ofFn] at hold
  have hgsize := oldOutput_length_le G e v
  have hnew := MachineOverlayRows.vertexSteps_le d e v.val (n * e)
    (List.ofFn (expanderValues H v)) (by
      intro j hj
      obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hj
      exact MachineOverlayRows.expanderValues_bounded H v p) (out ++ oldOutput G e v)
  simp only [List.length_ofFn, List.length_append] at hnew
  have hv := v.isLt.le
  have hsize : MachineOverlayRows.rowSizeBound d e v.val (n * e) ≤ expanderSize d e n := by
    unfold expanderSize MachineOverlayRows.rowSizeBound
    omega
  have hcost : MachineOverlayRows.rowCostBound d e v.val (n * e) ≤
      MachineOverlayRows.rowCostBound d e n (n * e) := by
    unfold MachineOverlayRows.rowCostBound
    change _ ≤ 8 * (n * e) + 4 * expanderSize d e n + _ + _ + 28
    omega
  have hsizeMul := Nat.mul_le_mul_left e hsize
  have holdBudget := Nat.mul_le_mul_left d
    (show MachineLazyRows.rowCostBound (d + e) 0 n (n * d) +
        2 * (out.length + d * MachineLazyRows.rowSizeBound (d + e) 0 n (n * d)) + 1 ≤
      MachineLazyRows.rowCostBound (d + e) 0 n (n * d) +
        2 * (outputCapacity d e n + d * oldSize d e n) + 1 by
      unfold oldSize
      omega)
  have hnewBudget := Nat.mul_le_mul_left e
    (show MachineOverlayRows.rowCostBound d e v.val (n * e) +
        2 * (out.length + (oldOutput G e v).length + e * MachineOverlayRows.rowSizeBound d e v.val (n * e)) + 1 ≤
      MachineOverlayRows.rowCostBound d e n (n * e) +
        2 * (outputCapacity d e n + d * oldSize d e n + e * expanderSize d e n) + 1 by omega)
  unfold pairSteps pairBudget oldRows
  omega

end IndependentSetsGames.Foundations.Complexity.MachineOverlayTable

end OAI
