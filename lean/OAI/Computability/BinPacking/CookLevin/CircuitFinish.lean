import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.CookLevin.CircuitEncodingBridge

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish

open Turing MachineComposition
open MachineCloudPadding

inductive Tape
  | current | freeInputs | root | reversedRecords | output | gateCount | scratch
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.current, .freeInputs, .root, .reversedRecords,
  .output, .gateCount, .scratch]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | copyOut | copyBack | cancel | records
  | rootOut | rootBack | countOut | countBack | currentOut | currentBack
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyOut, .copyBack, .cancel, .records, .rootOut,
  .rootBack, .countOut, .countBack, .currentOut, .currentBack]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := σ × Option Bool

def memory (current freeInputs root reversedRecords output gateCount scratch : List Bool) :
    Tape → List Bool
  | .current => current
  | .freeInputs => freeInputs
  | .root => root
  | .reversedRecords => reversedRecords
  | .output => output
  | .gateCount => gateCount
  | .scratch => scratch

@[simp] theorem update_current (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) .current x = memory x b c d e f g := by
  funext t; cases t <;> rfl
@[simp] theorem update_freeInputs (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) .freeInputs x = memory a x c d e f g := by
  funext t; cases t <;> rfl
@[simp] theorem update_root (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) .root x = memory a b x d e f g := by
  funext t; cases t <;> rfl
@[simp] theorem update_reversedRecords (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) .reversedRecords x = memory a b c x e f g := by
  funext t; cases t <;> rfl
@[simp] theorem update_output (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) .output x = memory a b c d x f g := by
  funext t; cases t <;> rfl
@[simp] theorem update_gateCount (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) .gateCount x = memory a b c d e x g := by
  funext t; cases t <;> rfl
@[simp] theorem update_scratch (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) .scratch x = memory a b c d e f x := by
  funext t; cases t <;> rfl

variable {σ : Type}

def cancelLoop : TM2.Stmt Alphabet Label (State σ) :=
  .pop .freeInputs (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop .gateCount (fun state _ => (state.1, none)) (.goto fun _ => .cancel))
      (.load (fun state => (state.1, none)) (.goto fun _ => .records)))

def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .copyOut => Reduction.MachineTransfer.loopAt .current .scratch id false
      .copyOut (some .copyBack)
  | .copyBack => MachineCopy.forkLoop .scratch .current .gateCount false
      .copyBack (some .cancel)
  | .cancel => cancelLoop
  | .records => Reduction.MachineTransfer.loopAt .reversedRecords .output id false
      .records (some .rootOut)
  | .rootOut => Reduction.MachineTransfer.loopAt .root .scratch id false
      .rootOut (some .rootBack)
  | .rootBack => Reduction.MachineTransfer.loopAt .scratch .output id false
      .rootBack (some .countOut)
  | .countOut => Reduction.MachineTransfer.loopAt .gateCount .scratch id false
      .countOut (some .countBack)
  | .countBack => Reduction.MachineTransfer.loopAt .scratch .output id false
      .countBack (some .currentOut)
  | .currentOut => Reduction.MachineTransfer.loopAt .current .scratch id false
      .currentOut (some .currentBack)
  | .currentBack => Reduction.MachineTransfer.loopAt .scratch .output id false
      .currentBack none

private theorem appendTrace {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, first, second]

theorem prependTrace {K Λ α : Type} [DecidableEq K]
    (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (firstLabel secondLabel : Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (α × Option Bool))
    (atFirst : target firstLabel = Reduction.MachineTransfer.loopAt source scratch id false
      firstLabel (some secondLabel))
    (atSecond : target secondLabel = Reduction.MachineTransfer.loopAt scratch destination
      id false secondLabel exit)
    (base : K → List Bool) (scratchEmpty : base scratch = [])
    (ambient : α) (register : Option Bool) :
    (advance (TM2.step target))^[2 * ((base source).length + 1)]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Reduction.MachineTransfer.tapesAt source destination base []
          (base source ++ base destination)⟩ := by
  let mid := Reduction.MachineTransfer.tapesAt source scratch base [] (base source).reverse
  have first := Reduction.MachineTransfer.transferAt_fromTapes source scratch sourceScratch
    id false firstLabel (some secondLabel) target atFirst base ambient register
  change (advance (TM2.step target))^[(base source).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) = _ at first
  simp only [List.map_id, scratchEmpty, List.append_nil] at first
  change (advance (TM2.step target))^[(base source).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨some secondLabel, (ambient, none), mid⟩ at first
  have hscratch : mid scratch = (base source).reverse := by
    simp [mid]
  have hdestination : mid destination = base destination := by
    simp [mid, Reduction.MachineTransfer.tapesAt, Ne.symm sourceDestination,
      destinationScratch]
  have second := Reduction.MachineTransfer.transferAt_fromTapes scratch destination
    (Ne.symm destinationScratch) id false secondLabel exit target atSecond mid ambient none
  change (advance (TM2.step target))^[(mid scratch).length + 1]
    (some ⟨some secondLabel, (ambient, none), mid⟩) = _ at second
  rw [hscratch, hdestination] at second
  simp only [List.length_reverse, List.reverse_reverse, List.map_id] at second
  have restored : Reduction.MachineTransfer.tapesAt scratch destination mid []
      (base source ++ base destination) =
      Reduction.MachineTransfer.tapesAt source destination base []
        (base source ++ base destination) := by
    funext k
    by_cases hs : k = source
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, mid, sourceDestination, sourceScratch]
    · by_cases hd : k = destination
      · subst k
        simp [Reduction.MachineTransfer.tapesAt]
      · by_cases ht : k = scratch
        · subst k
          simp [Reduction.MachineTransfer.tapesAt, Ne.symm sourceScratch,
            Ne.symm destinationScratch, scratchEmpty]
        · simp [Reduction.MachineTransfer.tapesAt, mid, hs, hd, ht]
  rw [restored] at second
  have both := appendTrace _ first second
  simpa only [show ((base source).length + 1) + ((base source).length + 1) =
    2 * ((base source).length + 1) by omega] using both

theorem cancelStep_zero (current root reversedRecords output scratch : List Bool)
    (g : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .cancel, (ambient, register),
        memory current (encodeWord 0) root reversedRecords output (encodeWord g) scratch⟩ =
      some ⟨some .records, (ambient, none),
        memory current [] root reversedRecords output (encodeWord g) scratch⟩ := by
  change some (TM2.stepAux cancelLoop _ _) = _
  simp [cancelLoop, TM2.stepAux, memory, encodeWord]

theorem cancelStep_succ (current root reversedRecords output scratch : List Bool)
    (f g : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .cancel, (ambient, register),
        memory current (encodeWord (f + 1)) root reversedRecords output
          (encodeWord (g + 1)) scratch⟩ =
      some ⟨some .cancel, (ambient, none),
        memory current (encodeWord f) root reversedRecords output (encodeWord g) scratch⟩ := by
  change some (TM2.stepAux cancelLoop _ _) = _
  simp [cancelLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

theorem cancelTrace (current root reversedRecords output scratch : List Bool)
    (f g : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[f + 1]
      (some ⟨some .cancel, (ambient, register),
        memory current (encodeWord f) root reversedRecords output
          (encodeWord (f + g)) scratch⟩) =
      some ⟨some .records, (ambient, none),
        memory current [] root reversedRecords output (encodeWord g) scratch⟩ := by
  induction f generalizing register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, advance_some] using
      cancelStep_zero current root reversedRecords output scratch g ambient register
  | succ f ih =>
    rw [Function.iterate_succ_apply]
    simp only [Nat.succ_add]
    change (advance (TM2.step program))^[f + 1]
      (TM2.step program
        ⟨some .cancel, (ambient, register),
          memory current (encodeWord (f + 1)) root reversedRecords output
            (encodeWord ((f + g) + 1)) scratch⟩) = _
    rw [cancelStep_succ]
    exact ih none

def initialTapes (n f root : Nat) (records : List Bool) : Tape → List Bool :=
  memory (encodeWord n) (encodeWord f) (encodeWord root) records.reverse [] [] []

def finalTapes (n f root : Nat) (records : List Bool) : Tape → List Bool :=
  memory [] [] [] [] (encodeWords [n, n - f, root] ++ records) [] []

def totalTime (n f root recordLength : Nat) : Nat :=
  2 * (n + 2) + (f + 1) + (recordLength + 1) +
    2 * (root + 2) + 2 * (n - f + 2) + 2 * (n + 2)

theorem finishTrace (n f root : Nat) (records : List Bool) (hf : f ≤ n)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime n f root records.length]
      (some ⟨some .copyOut, (ambient, register), initialTapes n f root records⟩) =
      some ⟨none, (ambient, none), finalTapes n f root records⟩ := by
  have copy := MachineCopy.copyTrace Tape.current Tape.gateCount Tape.scratch
    (by decide) (by decide) (by decide) false Label.copyOut Label.copyBack
    (some Label.cancel) program rfl rfl (initialTapes n f root records) rfl ambient register
  simp only [initialTapes, memory, encodeWord_length, List.append_nil, update_gateCount] at copy
  have cancel := cancelTrace (encodeWord n) (encodeWord root) records.reverse [] []
    f (n - f) ambient none
  rw [show f + (n - f) = n by omega] at cancel
  have reverse := Reduction.MachineTransfer.transferAt_fromTapes Tape.reversedRecords
    Tape.output (by decide) id false Label.records (some Label.rootOut) program rfl
    (memory (encodeWord n) [] (encodeWord root) records.reverse [] (encodeWord (n - f)) [])
    ambient none
  change (advance (TM2.step program))^[_]
    (some ⟨some .records, (ambient, none), _⟩) = _ at reverse
  simp only [memory, List.length_reverse, List.reverse_reverse, List.map_id,
    List.append_nil, Reduction.MachineTransfer.tapesAt, update_reversedRecords,
    update_output] at reverse
  have rootPhase := prependTrace Tape.root Tape.output Tape.scratch
    (by decide) (by decide) (by decide) Label.rootOut Label.rootBack (some Label.countOut)
    program rfl rfl
    (memory (encodeWord n) [] (encodeWord root) [] records (encodeWord (n - f)) [])
    rfl ambient none
  simp only [memory, encodeWord_length, Reduction.MachineTransfer.tapesAt,
    update_root, update_output] at rootPhase
  have countPhase := prependTrace Tape.gateCount Tape.output Tape.scratch
    (by decide) (by decide) (by decide) Label.countOut Label.countBack (some Label.currentOut)
    program rfl rfl
    (memory (encodeWord n) [] [] [] (encodeWord root ++ records) (encodeWord (n - f)) [])
    rfl ambient none
  simp only [memory, encodeWord_length, Reduction.MachineTransfer.tapesAt,
    update_gateCount, update_output] at countPhase
  have currentPhase := prependTrace Tape.current Tape.output Tape.scratch
    (by decide) (by decide) (by decide) Label.currentOut Label.currentBack none
    program rfl rfl
    (memory (encodeWord n) [] [] []
      (encodeWord (n - f) ++ (encodeWord root ++ records)) [] []) rfl ambient none
  simp only [memory, encodeWord_length, Reduction.MachineTransfer.tapesAt,
    update_current, update_output] at currentPhase
  have all := appendTrace _ (appendTrace _ (appendTrace _
    (appendTrace _ (appendTrace _ copy cancel) reverse) rootPhase) countPhase) currentPhase
  simpa only [totalTime, initialTapes, finalTapes, encodeWords,
    List.append_nil, List.append_assoc, Nat.add_assoc] using all

theorem finalTapes_output (n f root : Nat) (records : List Bool) :
    finalTapes n f root records .output = encodeWords [n, n - f, root] ++ records := rfl

theorem finalTapes_clean (n f root : Nat) (records : List Bool) (tape : Tape)
    (h : tape ≠ .output) : finalTapes n f root records tape = [] := by
  cases tape <;> simp_all [finalTapes, memory]

theorem totalTime_eq (n f root recordLength : Nat) :
    totalTime n f root recordLength = 4 * n + f + 2 * root + 2 * (n - f) + recordLength + 18 := by
  unfold totalTime
  ring

theorem totalTime_le (n f root recordLength : Nat) (hf : f ≤ n) (hr : root < n) :
    totalTime n f root recordLength ≤ 9 * n + recordLength + 18 := by
  rw [totalTime_eq]
  have hg := Nat.sub_le n f
  omega

theorem circuit_finalTapes (C : Circuit) :
    finalTapes C.wires C.inputs C.output.val (recordsBits C.records) =
      memory [] [] [] [] (circuitBits C) [] [] := by
  have hcount : C.wires - C.inputs = C.gates.length := by
    simp [Circuit.wires]
  simp only [finalTapes, hcount, circuitBits, circuitWords, encodeWords_append,
    recordsBits]

theorem circuitTrace (C : Circuit) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[
      totalTime C.wires C.inputs C.output.val (recordsBits C.records).length]
      (some ⟨some .copyOut, (ambient, register),
        initialTapes C.wires C.inputs C.output.val (recordsBits C.records)⟩) =
      some ⟨none, (ambient, none), memory [] [] [] [] (circuitBits C) [] []⟩ := by
  rw [← circuit_finalTapes]
  exact finishTrace C.wires C.inputs C.output.val (recordsBits C.records)
    (Nat.le_add_right _ _) ambient register

def circuitInTime (C : Circuit) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, (ambient, register),
        initialTapes C.wires C.inputs C.output.val (recordsBits C.records)⟩
      (some ⟨none, (ambient, none), memory [] [] [] [] (circuitBits C) [] []⟩)
      (9 * C.wires + (recordsBits C.records).length + 18) where
  steps := totalTime C.wires C.inputs C.output.val (recordsBits C.records).length
  evals_in_steps := circuitTrace C ambient register
  steps_le_m := totalTime_le _ _ _ _ (Nat.le_add_right _ _) C.output.isLt

def placedCircuitInTime {K Λ : Type} [DecidableEq K]
    (tape : Tape → K) (view : K → Option Tape)
    (left : ∀ t, view (tape t) = some t)
    (right : ∀ k t, view k = some t → tape t = k)
    (labels : Label → Λ) (exit : Option Λ) (extra : K → List Bool)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : ∀ l, target (labels l) = Placement.statement tape labels exit (program l))
    (C : Circuit) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      (Placement.configuration view labels exit extra
        ⟨some .copyOut, (ambient, register),
          initialTapes C.wires C.inputs C.output.val (recordsBits C.records)⟩)
      (some (Placement.configuration view labels exit extra
        ⟨none, (ambient, none), memory [] [] [] [] (circuitBits C) [] []⟩))
      (9 * C.wires + (recordsBits C.records).length + 18) :=
  liftExecutionInTime (TM2.step program) (TM2.step target)
    (Placement.configuration view labels exit extra)
    (Placement.step_simulation tape view left right labels exit extra program target code)
    (circuitInTime C ambient register)

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish

end OAI
