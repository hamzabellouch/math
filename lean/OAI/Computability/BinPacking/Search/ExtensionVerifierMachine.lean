import Mathlib.Tactic.DeriveFintype
import OAI.Computability.BinPacking.Arithmetic.GraphTallyMachine

namespace OAI

namespace BinPackingGap.ExtensionVerifierMachine.Fields

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer

inductive Block
  | bins | items | fixed
  deriving DecidableEq

protected abbrev Block.enumList : List Block := [.bins, .items, .fixed]

protected theorem Block.enumList_getElem?_ctorIdx_eq (x : Block) :
    Block.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Block.enumList_nodup : Block.enumList.Nodup := by decide

instance : Fintype Block where
  elems := ⟨Block.enumList, Block.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Field
  | bins | numerator | denominator
  deriving DecidableEq

protected abbrev Field.enumList : List Field := [.bins, .numerator, .denominator]

protected theorem Field.enumList_getElem?_ctorIdx_eq (x : Field) :
    Field.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Field.enumList_nodup : Field.enumList.Nodup := by decide

instance : Fintype Field where
  elems := ⟨Field.enumList, Field.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Mode
  | flag (field : Field)
  | digit (field : Field)
  | items
  | fixed
  deriving DecidableEq, Fintype

def Field.block : Field → Block
  | .bins => .bins
  | .numerator | .denominator => .items

def afterField : Field → Mode
  | .bins => .items
  | .numerator => .flag .denominator
  | .denominator => .items

def Mode.block : Mode → Block
  | .flag f | .digit f => f.block
  | .items => .items
  | .fixed => .fixed

def nextMode : Mode → Bool → Mode
  | .flag f, true => .digit f
  | .flag f, false => afterField f
  | .digit f, _ => .flag f
  | .items, true => .flag .numerator
  | .items, false => .fixed
  | .fixed, _ => .fixed

abbrev Words := Block → List Bool

def prepend (words : Words) (block : Block) (chunk : List Bool) : Words :=
  Function.update words block (chunk ++ words block)

@[simp] theorem prepend_nil (words : Words) (block : Block) :
    prepend words block [] = words := by
  simp [prepend]

theorem prepend_prepend (words : Words) (block : Block) (first second : List Bool) :
    prepend (prepend words block first) block second =
      prepend words block (second ++ first) := by
  funext k
  by_cases h : k = block
  · subst k; simp [prepend, List.append_assoc]
  · simp [prepend, h]

def run : Mode → Words → List Bool → Mode × Words
  | mode, words, [] => (mode, words)
  | mode, words, bit :: rest =>
      run (nextMode mode bit) (prepend words mode.block [bit]) rest

theorem run_frame (field : Field) (bits suffix : List Bool) (words : Words) :
    run (.flag field) words (BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix) =
      run (afterField field)
        (prepend words field.block (BinPackingCompleteness.BinaryEncoding.frame bits).reverse)
        suffix := by
  induction bits generalizing words with
  | nil => simp [BinPackingCompleteness.BinaryEncoding.frame, run, nextMode, Mode.block]
  | cons bit bits ih =>
      simp only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append, run,
        nextMode, Mode.block]
      rw [ih]
      simp only [prepend_prepend, List.reverse_cons, List.append_assoc,
        List.singleton_append]

theorem run_nat (field : Field) (n : Nat) (suffix : List Bool) (words : Words) :
    run (.flag field) words (BinaryEncoding.natBits n ++ suffix) =
      run (afterField field)
        (prepend words field.block (BinaryEncoding.natBits n).reverse) suffix :=
  run_frame field n.bits suffix words

theorem run_items (items : RawInstance) (suffix : List Bool) (words : Words) :
    run .items words (BinaryEncoding.rawInstanceBits items ++ suffix) =
      run .fixed
        (prepend words .items (BinaryEncoding.rawInstanceBits items).reverse) suffix := by
  induction items generalizing words with
  | nil => simp [BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits, run,
      nextMode, Mode.block]
  | cons item items ih =>
      change run (.flag .numerator) (prepend words .items [true])
        (BinaryEncoding.natBits item.1 ++ BinaryEncoding.natBits item.2 ++
          BinaryEncoding.rawInstanceBits items ++ suffix) = _
      simp only [List.append_assoc]
      rw [run_nat]
      change run (.flag .denominator)
        (prepend (prepend words .items [true]) .items
          (BinaryEncoding.natBits item.1).reverse)
        (BinaryEncoding.natBits item.2 ++
          (BinaryEncoding.rawInstanceBits items ++ suffix)) = _
      rw [run_nat]
      change run .items _ (BinaryEncoding.rawInstanceBits items ++ suffix) = _
      rw [ih]
      simp only [Field.block, prepend_prepend, BinaryEncoding.rawInstanceBits,
        BinaryEncoding.listBits, BinaryEncoding.pairBits, List.reverse_cons,
        List.reverse_append, List.append_assoc]

theorem run_fixed (input : List Bool) (words : Words) :
    run .fixed words input = (.fixed, prepend words .fixed input.reverse) := by
  induction input generalizing words with
  | nil => simp [run]
  | cons bit input ih =>
      simpa only [run, nextMode, Mode.block, prepend_prepend,
        List.reverse_cons] using ih (prepend words .fixed [bit])

def encodedWords (bins : Nat) (items : RawInstance) (fixed : List (Option Nat)) : Words
  | .bins => BinaryEncoding.natBits bins
  | .items => BinaryEncoding.rawInstanceBits items
  | .fixed => BinaryEncoding.listBits (BinaryEncoding.optionBits BinaryEncoding.natBits) fixed

def empty : Words := fun _ => []

def reversed (words : Words) : Words := fun block => (words block).reverse

@[simp] theorem reversed_reversed (words : Words) : reversed (reversed words) = words := by
  funext block
  simp [reversed]

def wordLength (words : Words) : Nat :=
  (words .bins).length + (words .items).length + (words .fixed).length

@[simp] theorem wordLength_empty : wordLength empty = 0 := rfl

@[simp] theorem wordLength_reversed (words : Words) :
    wordLength (reversed words) = wordLength words := by simp [wordLength, reversed]

theorem wordLength_prepend (words : Words) (block : Block) (chunk : List Bool) :
    wordLength (prepend words block chunk) = wordLength words + chunk.length := by
  cases block <;> simp [wordLength, prepend] <;> omega

theorem run_wordLength (mode : Mode) (words : Words) (input : List Bool) :
    wordLength (run mode words input).2 = wordLength words + input.length := by
  induction input generalizing mode words with
  | nil => simp [run]
  | cons bit input ih =>
      rw [run, ih, wordLength_prepend]
      simp only [List.length_cons, List.length_nil]
      omega

theorem run_extension (bins : Nat) (items : RawInstance) (fixed : List (Option Nat)) :
    run (.flag .bins) empty (BinaryEncoding.extensionBits bins items fixed) =
      (.fixed, reversed (encodedWords bins items fixed)) := by
  unfold BinaryEncoding.extensionBits
  rw [List.append_assoc, run_nat]
  change run .items _ (_ ++ _) = _
  rw [run_items, run_fixed]
  congr 1
  funext block
  cases block <;> simp [prepend, empty, reversed, encodedWords, Field.block]

inductive Label
  | scan | restoreBins | restoreItems | restoreFixed
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .restoreBins, .restoreItems,
  .restoreFixed]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Fin 7) := Bool
abbrev State := Mode × Option Bool

def scanFinish : TM2.Stmt Alphabet Label State :=
  .load (fun state => (nextMode state.1 (state.2.getD false), none))
    (.goto fun _ => .scan)

def instruction : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop 0 (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.branch (fun state => decide (state.1.block = .bins))
            (.push 1 (fun state => state.2.getD false) scanFinish)
            (.branch (fun state => decide (state.1.block = .items))
              (.push 2 (fun state => state.2.getD false) scanFinish)
              (.push 3 (fun state => state.2.getD false) scanFinish)))
          (.load (fun _ => (.flag .bins, none)) (.goto fun _ => .restoreBins)))
  | .restoreBins => loopAt 1 4 id false .restoreBins (some .restoreItems)
  | .restoreItems => loopAt 2 5 id false .restoreItems (some .restoreFixed)
  | .restoreFixed => loopAt 3 6 id false .restoreFixed none

abbrev machine : FinTM2 where
  K := Fin 7
  k₀ := 0
  k₁ := 4
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := (.flag .bins, none)
  m := instruction

def tapes (input : List Bool) (saved output : Words) : Fin 7 → List Bool
  | 0 => input
  | 1 => saved .bins
  | 2 => saved .items
  | 3 => saved .fixed
  | 4 => output .bins
  | 5 => output .items
  | _ => output .fixed

def cfg (label : Option Label) (input : List Bool) (saved output : Words)
    (mode : Mode := .flag .bins) (register : Option Bool := none) : machine.Cfg :=
  ⟨label, (mode, register), tapes input saved output⟩

private theorem update_input (input replacement : List Bool) (saved output : Words) :
    Function.update (tapes input saved output) 0 replacement =
      tapes replacement saved output := by
  funext k; fin_cases k <;> rfl

def savedTape : Block → Fin 7
  | .bins => 1
  | .items => 2
  | .fixed => 3

def outputTape : Block → Fin 7
  | .bins => 4
  | .items => 5
  | .fixed => 6

private theorem update_saved (input : List Bool) (saved output : Words)
    (block : Block) (replacement : List Bool) :
    Function.update (tapes input saved output) (savedTape block) replacement =
      tapes input (Function.update saved block replacement) output := by
  funext k; cases block <;> fin_cases k <;> rfl

private theorem update_output (input : List Bool) (saved output : Words)
    (block : Block) (replacement : List Bool) :
    Function.update (tapes input saved output) (outputTape block) replacement =
      tapes input saved (Function.update output block replacement) := by
  funext k; cases block <;> fin_cases k <;> rfl

theorem step_scan_empty (saved output : Words) (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) [] saved output mode register) =
      some (cfg (some .restoreBins) [] saved output) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  simp [instruction, cfg, TM2.stepAux, tapes, update_input]
  all_goals rfl

theorem step_scan_cons (bit : Bool) (input : List Bool) (saved output : Words)
    (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) (bit :: input) saved output mode register) =
      some (cfg (some .scan) input (prepend saved mode.block [bit]) output
        (nextMode mode bit)) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  cases mode with
  | flag field =>
      cases field <;>
        simp [instruction, scanFinish, cfg, TM2.stepAux, Mode.block, Field.block,
          update_input, ← update_saved, savedTape, prepend, tapes] <;> rfl
  | digit field =>
      cases field <;>
        simp [instruction, scanFinish, cfg, TM2.stepAux, Mode.block, Field.block,
          update_input, ← update_saved, savedTape, prepend, tapes] <;> rfl
  | items =>
      simp [instruction, scanFinish, cfg, TM2.stepAux, Mode.block,
        update_input, ← update_saved, savedTape, prepend, tapes]; rfl
  | fixed =>
      simp [instruction, scanFinish, cfg, TM2.stepAux, Mode.block,
        update_input, ← update_saved, savedTape, prepend, tapes]; rfl

theorem scanTrace (input : List Bool) (saved output : Words) (mode : Mode)
    (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .scan) input saved output mode register)) =
      some (cfg (some .restoreBins) [] (run mode saved input).2 output) := by
  induction input generalizing mode saved register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        advance_some, run] using step_scan_empty saved output mode register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [step_scan_cons]
      simpa only [run] using ih (saved := prepend saved mode.block [bit])
        (mode := nextMode mode bit) (register := none)

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .scan) input empty empty := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem scan_extension (bins : Nat) (items : RawInstance) (fixed : List (Option Nat)) :
    (advance machine.step)^[(BinaryEncoding.extensionBits bins items fixed).length + 1]
      (some (initList machine (BinaryEncoding.extensionBits bins items fixed))) =
      some (cfg (some .restoreBins) [] (reversed (encodedWords bins items fixed)) empty) := by
  rw [initList_eq]
  simpa only [run_extension] using
    scanTrace (BinaryEncoding.extensionBits bins items fixed) empty empty (.flag .bins) none

def restoreLabel : Block → Label
  | .bins => .restoreBins
  | .items => .restoreItems
  | .fixed => .restoreFixed

def nextRestore : Block → Option Label
  | .bins => some .restoreItems
  | .items => some .restoreFixed
  | .fixed => none

theorem restoreTrace (block : Block) (saved output : Words) :
    (advance machine.step)^[(saved block).length + 1]
      (some (cfg (some (restoreLabel block)) [] saved output)) =
      some (cfg (nextRestore block) [] (Function.update saved block [])
        (prepend output block (saved block).reverse)) := by
  change (nextAt (outputTape block) instruction)^[(saved block).length + 1]
    (some (cfg (some (restoreLabel block)) [] saved output)) =
    some (cfg (nextRestore block) [] (Function.update saved block [])
      (prepend output block (saved block).reverse))
  have distinct : savedTape block ≠ outputTape block := by cases block <;> decide
  have atLoop : instruction (restoreLabel block) =
      loopAt (savedTape block) (outputTape block) id false
        (restoreLabel block) (nextRestore block) := by cases block <;> rfl
  have trace := transferAt_fromTapes (savedTape block) (outputTape block) distinct
    id false (restoreLabel block) (nextRestore block) instruction atLoop
    (tapes [] saved output) (Mode.flag .bins) none
  have source : tapes [] saved output (savedTape block) = saved block := by
    cases block <;> rfl
  have destination : tapes [] saved output (outputTape block) = output block := by
    cases block <;> rfl
  rw [source, destination] at trace
  simpa only [cfg, tapesAt, update_saved, update_output,
    List.map_id_fun, id_eq, prepend] using! trace

private theorem appendTrace {X : Type*} (f : X → X) {a b : Nat} {x y z : X}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, first, second]

theorem restoreAllTrace (words : Words) :
    (advance machine.step)^[(words .bins).length + (words .items).length +
        (words .fixed).length + 3]
      (some (cfg (some .restoreBins) [] (reversed words) empty)) =
      some (cfg none [] empty words) := by
  let saved₁ := Function.update (reversed words) .bins []
  let output₁ := prepend empty .bins (words .bins)
  let saved₂ := Function.update saved₁ .items []
  let output₂ := prepend output₁ .items (words .items)
  have first := restoreTrace .bins (reversed words) empty
  have second := restoreTrace .items saved₁ output₁
  have third := restoreTrace .fixed saved₂ output₂
  simp only [reversed, List.length_reverse, List.reverse_reverse,
    restoreLabel, nextRestore] at first
  change (advance machine.step)^[(words .bins).length + 1]
    (some (cfg (some .restoreBins) [] (reversed words) empty)) =
    some (cfg (some .restoreItems) [] saved₁ output₁) at first
  have saved₁_items : saved₁ .items = (words .items).reverse := by
    simp [saved₁, reversed]
  have saved₂_fixed : saved₂ .fixed = (words .fixed).reverse := by
    simp [saved₂, saved₁, reversed]
  rw [saved₁_items] at second
  simp only [List.length_reverse, List.reverse_reverse, restoreLabel, nextRestore] at second
  change (advance machine.step)^[(words .items).length + 1]
    (some (cfg (some .restoreItems) [] saved₁ output₁)) =
    some (cfg (some .restoreFixed) [] saved₂ output₂) at second
  rw [saved₂_fixed] at third
  simp only [List.length_reverse, List.reverse_reverse, restoreLabel, nextRestore] at third
  have cleared : Function.update saved₂ .fixed [] = empty := by
    funext block; cases block <;> simp [saved₂, saved₁, empty]
  have restored : prepend output₂ .fixed (words .fixed) = words := by
    funext block; cases block <;> simp [output₂, output₁, prepend, empty]
  rw [cleared, restored] at third
  have total := appendTrace (advance machine.step)
    (appendTrace (advance machine.step) first second) third
  have clock : (words .bins).length + (words .items).length +
      (words .fixed).length + 3 =
      ((words .bins).length + 1 + ((words .items).length + 1)) +
        ((words .fixed).length + 1) := by omega
  rw [clock]
  exact total

theorem extensionTrace (bins : Nat) (items : RawInstance) (fixed : List (Option Nat)) :
    (advance machine.step)^[2 * (BinaryEncoding.extensionBits bins items fixed).length + 4]
      (some (initList machine (BinaryEncoding.extensionBits bins items fixed))) =
      some (cfg none [] empty (encodedWords bins items fixed)) := by
  have first := scan_extension bins items fixed
  have second := restoreAllTrace (encodedWords bins items fixed)
  have joined := appendTrace (advance machine.step) first second
  have length : (BinaryEncoding.extensionBits bins items fixed).length =
      (encodedWords bins items fixed .bins).length +
      (encodedWords bins items fixed .items).length +
      (encodedWords bins items fixed .fixed).length := by
    simp [BinaryEncoding.extensionBits, encodedWords, Nat.add_assoc]
  have clock : 2 * (BinaryEncoding.extensionBits bins items fixed).length + 4 =
      (BinaryEncoding.extensionBits bins items fixed).length + 1 +
        ((encodedWords bins items fixed .bins).length +
          (encodedWords bins items fixed .items).length +
          (encodedWords bins items fixed .fixed).length + 3) := by omega
  rw [clock]
  exact joined

def extensionInTime (bins : Nat) (items : RawInstance) (fixed : List (Option Nat)) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (BinaryEncoding.extensionBits bins items fixed))
      (some (cfg none [] empty (encodedWords bins items fixed)))
      (2 * (BinaryEncoding.extensionBits bins items fixed).length + 4) where
  steps := 2 * (BinaryEncoding.extensionBits bins items fixed).length + 4
  evals_in_steps := extensionTrace bins items fixed
  steps_le_m := Nat.le_refl _

def extracted (input : List Bool) : Words :=
  reversed (run (.flag .bins) empty input).2

theorem totalTrace (input : List Bool) :
    (advance machine.step)^[2 * input.length + 4]
      (some (initList machine input)) =
      some (cfg none [] empty (extracted input)) := by
  have first := scanTrace input empty empty (.flag .bins) none
  have second := restoreAllTrace (extracted input)
  have startSaved : reversed (extracted input) = (run (.flag .bins) empty input).2 :=
    reversed_reversed _
  rw [startSaved] at second
  have joined := appendTrace (advance machine.step) first second
  rw [initList_eq]
  have length : wordLength (extracted input) = input.length := by
    simp [extracted, run_wordLength]
  unfold wordLength at length
  have clock : 2 * input.length + 4 = input.length + 1 +
      ((extracted input .bins).length + (extracted input .items).length +
        (extracted input .fixed).length + 3) := by omega
  rw [clock]
  exact joined

def extractionInTime (input : List Bool) :
    StateTransition.EvalsToInTime machine.step (initList machine input)
      (some (cfg none [] empty (extracted input))) (2 * input.length + 4) where
  steps := 2 * input.length + 4
  evals_in_steps := totalTrace input
  steps_le_m := Nat.le_refl _

@[simp] theorem extracted_extension (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) :
    extracted (BinaryEncoding.extensionBits bins items fixed) =
      encodedWords bins items fixed := by
  simp [extracted, run_extension]

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end BinPackingGap.ExtensionVerifierMachine.Fields

end OAI
