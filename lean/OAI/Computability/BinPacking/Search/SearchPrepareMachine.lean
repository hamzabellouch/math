import OAI.Computability.BinPacking.Arithmetic.BinaryTallyMachine
import OAI.Computability.BinPacking.Machines.FrameEmitMachine
import OAI.Computability.BinPacking.Search.SearchFixedReplaceMachine

namespace OAI

namespace BinPackingGap.SearchPrepareMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open SearchSemantics SearchEncoding BinaryEncoding SearchMachineComposition
open BinPackingGames.Reduction.MachineTransfer

inductive Tape
  | input | binary | scratch | index | payload | reversed | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .binary, .scratch, .index, .payload,
  .reversed, .output]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | save | saveRestore | frameSaved | phase
  | convertBins (label : UnaryToBinaryMachine.Label)
  | emitBins | seedIndex | index
  | convertLabel (label : UnaryToBinaryMachine.Label)
  | emitLabel | restoreLabel
  | items | numerator | numeratorDigit | denominator | denominatorDigit
  | dispatch
  | replace (label : SearchFixedReplaceMachine.Label)
  | fixed | reverse
  deriving DecidableEq, Fintype

abbrev Register := Bool × Option Bool

def tapes (input binary scratch index payload reversed output : List Bool) : Tape → List Bool
  | .input => input
  | .binary => binary
  | .scratch => scratch
  | .index => index
  | .payload => payload
  | .reversed => reversed
  | .output => output

@[simp] theorem tapes_input (a b c d e f g : List Bool) :
    tapes a b c d e f g .input = a := rfl

@[simp] theorem update_input (a b c d e f g x : List Bool) :
    Function.update (tapes a b c d e f g) .input x =
      tapes x b c d e f g := by
  funext k; cases k <;> rfl

@[simp] theorem tapes_binary (a b c d e f g : List Bool) :
    tapes a b c d e f g .binary = b := rfl

@[simp] theorem update_binary (a b c d e f g x : List Bool) :
    Function.update (tapes a b c d e f g) .binary x =
      tapes a x c d e f g := by
  funext k; cases k <;> rfl

@[simp] theorem tapes_scratch (a b c d e f g : List Bool) :
    tapes a b c d e f g .scratch = c := rfl

@[simp] theorem update_scratch (a b c d e f g x : List Bool) :
    Function.update (tapes a b c d e f g) .scratch x =
      tapes a b x d e f g := by
  funext k; cases k <;> rfl

@[simp] theorem tapes_index (a b c d e f g : List Bool) :
    tapes a b c d e f g .index = d := rfl

@[simp] theorem update_index (a b c d e f g x : List Bool) :
    Function.update (tapes a b c d e f g) .index x =
      tapes a b c x e f g := by
  funext k; cases k <;> rfl

@[simp] theorem tapes_payload (a b c d e f g : List Bool) :
    tapes a b c d e f g .payload = e := rfl

@[simp] theorem update_payload (a b c d e f g x : List Bool) :
    Function.update (tapes a b c d e f g) .payload x =
      tapes a b c d x f g := by
  funext k; cases k <;> rfl

@[simp] theorem tapes_reversed (a b c d e f g : List Bool) :
    tapes a b c d e f g .reversed = f := rfl

@[simp] theorem update_reversed (a b c d e f g x : List Bool) :
    Function.update (tapes a b c d e f g) .reversed x =
      tapes a b c d e x g := by
  funext k; cases k <;> rfl

@[simp] theorem tapes_output (a b c d e f g : List Bool) :
    tapes a b c d e f g .output = g := rfl

@[simp] theorem update_output (a b c d e f g x : List Bool) :
    Function.update (tapes a b c d e f g) .output x =
      tapes a b c d e f x := by
  funext k; cases k <;> rfl

def go (next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .load (fun state => (state.1, none)) (.goto fun _ => next)

def replacePlace : SearchFixedReplaceMachine.Slot → Tape
  | .source => .input
  | .index => .index
  | .payload => .payload
  | .reversed => .reversed

theorem replacePlace_injective : Function.Injective replacePlace := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

def copyFlag (yes no : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .pop .input (fun state head => (state.1, head))
    (.push .reversed (fun state => state.2.getD false)
      (.branch (fun state => state.2.getD false) (go yes) (go no)))

def copyDigit (next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .pop .input (fun state head => (state.1, head))
    (.push .reversed (fun state => state.2.getD false) (go next))

def code : Label → TM2.Stmt (fun _ : Tape => Bool) Label Register
  | .save => loopAt .input .scratch id false .save (some .saveRestore)
  | .saveRestore => MachineCopy.forkLoop .scratch .input .payload false
      .saveRestore (some .frameSaved)
  | .frameSaved => FrameEmitMachine.instruction .payload .reversed .frameSaved (some .phase)
  | .phase => .pop .input (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false) (go .reverse)
        (.pop .input (fun state head => (state.1, head))
          (.load (fun state => (state.2.getD false, none))
            (.goto fun _ => .convertBins .scan))))
  | .convertBins label => UnaryToBinaryMachine.instruction .input .binary .scratch
      Label.convertBins (some .emitBins) label
  | .emitBins => FrameEmitMachine.instruction .binary .reversed .emitBins (some .seedIndex)
  | .seedIndex => .push .index (fun _ => false) (go .index)
  | .index => .pop .input (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.push .index (fun _ => true) (go .index))
        (go (.convertLabel .scan)))
  | .convertLabel label => UnaryToBinaryMachine.instruction .input .binary .scratch
      Label.convertLabel (some .emitLabel) label
  | .emitLabel => FrameEmitMachine.instruction .binary .scratch .emitLabel (some .restoreLabel)
  | .restoreLabel => loopAt .scratch .payload id false .restoreLabel (some .items)
  | .items => copyFlag .numerator .dispatch
  | .numerator => copyFlag .numeratorDigit .denominator
  | .numeratorDigit => copyDigit .numerator
  | .denominator => copyFlag .denominatorDigit .items
  | .denominatorDigit => copyDigit .denominator
  | .dispatch => .branch Prod.fst (go (.replace (.entry true))) (go .fixed)
  | .replace label => SearchFixedReplaceMachine.instruction replacePlace
      Label.replace (some .reverse) label
  | .fixed => loopAt .input .reversed id false .fixed (some .reverse)
  | .reverse => loopAt .reversed .output id false .reverse none

def program : MachineCanonicalOutput.Program Tape Label Register where
  input := .input
  output := .output
  main := .save
  initial := (false, none)
  code := code

abbrev machine := MachineCanonicalOutput.sourceMachine program

def cfg (label : Option Label) (fill : Bool)
    (input binary scratch index payload reversed output : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, (fill, register), tapes input binary scratch index payload reversed output⟩

private theorem oneStepTrace {a b : machine.Cfg} (h : machine.step a = some b) :
    (advance machine.step)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

private theorem actualStep : TM2.step code = machine.step := rfl

private theorem transferNext (dst : Tape) : nextAt dst code = advance machine.step := by
  funext state
  rfl

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem saveTrace (word : List Bool) :
    (advance machine.step)^[2 * (word.length + 1)]
      (some (cfg (some .save) false word [] [] [] [] [] [])) =
      some (cfg (some .frameSaved) false word [] [] [] word [] []) := by
  have h := MachineCopy.copyTrace (K := Tape) (σ := Bool) .input .payload .scratch
    (by decide) (by decide) (by decide) false .save .saveRestore (some .frameSaved)
    code rfl rfl (tapes word [] [] [] [] [] []) rfl false none
  rw [actualStep] at h
  simpa only [cfg, tapes_input, tapes_payload, update_payload, List.append_nil] using! h

theorem frameSavedTrace (word : List Bool) :
    (advance machine.step)^[word.length + 1]
      (some (cfg (some .frameSaved) false word [] [] [] word [] [])) =
      some (cfg (some .phase) false word [] [] [] []
        ((BinPackingCompleteness.BinaryEncoding.frame word).reverse) []) := by
  have h := FrameEmitMachine.trace (K := Tape) (A := Bool) .payload .reversed (by decide)
    .frameSaved (some .phase) code rfl (tapes word [] [] [] [] [] []) false word []
  rw [actualStep] at h
  simpa only [cfg, tapesAt, update_payload, update_reversed, List.append_nil] using! h

theorem phaseActive (fill : Bool) (word reversed : List Bool) :
    machine.step (cfg (some .phase) false (false :: fill :: word) [] [] [] [] reversed []) =
      some (cfg (some (.convertBins .scan)) fill word [] [] [] [] reversed []) := by
  change some (TM2.stepAux (code .phase) _ _) = _
  simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem phaseInactive (bit : Bool) (word reversed : List Bool) :
    machine.step (cfg (some .phase) false (true :: bit :: word) [] [] [] [] reversed []) =
      some (cfg (some .reverse) false (bit :: word) [] [] [] [] reversed []) := by
  change some (TM2.stepAux (code .phase) _ _) = _
  simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem convertBinsTrace (fill : Bool) (n : Nat) (word reversed : List Bool) :
    (advance machine.step)^[UnaryToBinaryMachine.steps n 0]
      (some (cfg (some (.convertBins .scan)) fill (encodeWord n ++ word)
        [] [] [] [] reversed [])) =
      some (cfg (some .emitBins) fill word n.bits [] [] [] reversed []) := by
  have h := UnaryToBinaryMachine.convertTrace (K := Tape) (A := Bool)
    .input .binary .scratch (by decide) (by decide) (by decide)
    Label.convertBins (some .emitBins) code (fun _ => rfl)
    (tapes [] [] [] [] [] reversed []) fill n 0 word
  rw [actualStep] at h
  simpa [UnaryToBinaryMachine.tapes, cfg] using! h

theorem emitBinsTrace (fill : Bool) (n : Nat) (word reversed : List Bool) :
    (advance machine.step)^[n.bits.length + 1]
      (some (cfg (some .emitBins) fill word n.bits [] [] [] reversed [])) =
      some (cfg (some .seedIndex) fill word [] [] [] []
        ((natBits n).reverse ++ reversed) []) := by
  have h := FrameEmitMachine.trace (K := Tape) (A := Bool) .binary .reversed (by decide)
    .emitBins (some .seedIndex) code rfl (tapes word [] [] [] [] [] []) fill n.bits reversed
  rw [actualStep] at h
  simpa only [cfg, tapesAt, update_binary, update_reversed, natBits,
    BinPackingCompleteness.BinaryEncoding.nameBits] using! h

theorem seedIndexStep (fill : Bool) (word reversed : List Bool) :
    machine.step (cfg (some .seedIndex) fill word [] [] [] [] reversed []) =
      some (cfg (some .index) fill word [] [] [false] [] reversed []) := by
  change some (TM2.stepAux (code .seedIndex) _ _) = _
  simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem indexStep (fill bit : Bool) (word index reversed : List Bool) :
    machine.step (cfg (some .index) fill (bit :: word) [] [] index [] reversed []) =
      some (cfg (some (if bit then .index else .convertLabel .scan))
        fill word [] [] (if bit then true :: index else index) [] reversed []) := by
  change some (TM2.stepAux (code .index) _ _) = _
  cases bit <;> simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem indexTrace (fill : Bool) (n m : Nat) (word reversed : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some .index) fill (encodeWord n ++ word) [] []
        (encodeWord m) [] reversed [])) =
      some (cfg (some (.convertLabel .scan)) fill word [] []
        (encodeWord (m + n)) [] reversed []) := by
  induction n generalizing m with
  | zero =>
      simpa only [encodeWord, List.replicate_zero, List.nil_append, List.singleton_append,
        Nat.zero_add, Nat.add_zero, Function.iterate_one, advance_some,
        Bool.false_eq_true, ↓reduceIte] using
        indexStep fill false word (encodeWord m) reversed
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp only [encodeWord, List.replicate_succ, List.cons_append, advance_some]
      rw [indexStep fill true]
      simpa only [encodeWord, List.replicate_succ, List.cons_append,
        Bool.true_eq, ↓reduceIte, Nat.add_assoc, Nat.add_comm 1 n] using ih (m + 1)

theorem convertLabelTrace (fill : Bool) (n : Nat) (word index reversed : List Bool) :
    (advance machine.step)^[UnaryToBinaryMachine.steps n 0]
      (some (cfg (some (.convertLabel .scan)) fill (encodeWord n ++ word)
        [] [] index [] reversed [])) =
      some (cfg (some .emitLabel) fill word n.bits [] index [] reversed []) := by
  have h := UnaryToBinaryMachine.convertTrace (K := Tape) (A := Bool)
    .input .binary .scratch (by decide) (by decide) (by decide)
    Label.convertLabel (some .emitLabel) code (fun _ => rfl)
    (tapes [] [] [] index [] reversed []) fill n 0 word
  rw [actualStep] at h
  simpa [UnaryToBinaryMachine.tapes, cfg] using! h

theorem emitLabelTrace (fill : Bool) (n : Nat) (word index reversed : List Bool) :
    (advance machine.step)^[n.bits.length + 1]
      (some (cfg (some .emitLabel) fill word n.bits [] index [] reversed [])) =
      some (cfg (some .restoreLabel) fill word [] (natBits n).reverse index [] reversed []) := by
  have h := FrameEmitMachine.trace (K := Tape) (A := Bool) .binary .scratch (by decide)
    .emitLabel (some .restoreLabel) code rfl (tapes word [] [] index [] reversed []) fill n.bits []
  rw [actualStep] at h
  simpa only [cfg, tapesAt, update_binary, update_scratch, natBits,
    BinPackingCompleteness.BinaryEncoding.nameBits, List.append_nil] using! h

theorem restoreLabelTrace (fill : Bool) (n : Nat) (word index reversed : List Bool) :
    (advance machine.step)^[(natBits n).length + 1]
      (some (cfg (some .restoreLabel) fill word [] (natBits n).reverse index [] reversed [])) =
      some (cfg (some .items) fill word [] [] index (natBits n) reversed []) := by
  have h := transferAt_fromTapes (Γ := fun _ : Tape => Bool) .scratch .payload (by decide)
    id false .restoreLabel (some .items) code rfl
    (tapes word [] (natBits n).reverse index [] reversed []) fill none
  simpa only [cfg, transferNext, tapes_scratch, tapes_payload, tapesAt,
    update_scratch, update_payload, List.length_reverse, List.reverse_reverse,
    List.map_id_fun, id_eq, List.append_nil] using! h

theorem copyFlagStep (yes no current : Label) (h : code current = copyFlag yes no)
    (fill bit : Bool) (a index payload reversed : List Bool) :
    machine.step (cfg (some current) fill (bit :: a) [] [] index payload reversed []) =
      some (cfg (some (if bit then yes else no)) fill a [] [] index payload
        (bit :: reversed) []) := by
  change some (TM2.stepAux (code current) _ _) = _
  rw [h]
  cases bit <;> simp [copyFlag, go, TM2.stepAux, cfg]
  all_goals rfl

theorem copyDigitStep (next current : Label) (h : code current = copyDigit next)
    (fill bit : Bool) (a index payload reversed : List Bool) :
    machine.step (cfg (some current) fill (bit :: a) [] [] index payload reversed []) =
      some (cfg (some next) fill a [] [] index payload (bit :: reversed) []) := by
  change some (TM2.stepAux (code current) _ _) = _
  rw [h]
  simp [copyDigit, go, TM2.stepAux, cfg]
  all_goals rfl

theorem copyNameTrace (current digit next : Label)
    (hc : code current = copyFlag digit next) (hd : code digit = copyDigit current)
    (fill : Bool) (bits a index payload reversed : List Bool) :
    (advance machine.step)^[(BinPackingCompleteness.BinaryEncoding.frame bits).length]
      (some (cfg (some current) fill (BinPackingCompleteness.BinaryEncoding.frame bits ++ a)
        [] [] index payload reversed [])) =
      some (cfg (some next) fill a [] [] index payload
        ((BinPackingCompleteness.BinaryEncoding.frame bits).reverse ++ reversed) []) := by
  induction bits generalizing reversed with
  | nil =>
      simpa [BinPackingCompleteness.BinaryEncoding.frame, advance] using!
        copyFlagStep digit next current hc fill false a index payload reversed
  | cons bit bits ih =>
      have first := copyFlagStep digit next current hc fill true
        (bit :: (BinPackingCompleteness.BinaryEncoding.frame bits ++ a)) index payload reversed
      have second := copyDigitStep current digit hd fill bit
        (BinPackingCompleteness.BinaryEncoding.frame bits ++ a) index payload (true :: reversed)
      simp only [↓reduceIte] at first
      have full := joinTrace (joinTrace
        (oneStepTrace first)
        (oneStepTrace second)) (ih (bit :: true :: reversed))
      have clock : 1 + 1 + (BinPackingCompleteness.BinaryEncoding.frame bits).length =
          (BinPackingCompleteness.BinaryEncoding.frame (bit :: bits)).length := by
        simp only [BinPackingCompleteness.BinaryEncoding.frame, List.length_cons]
        omega
      rw [clock] at full
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
        List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using full

theorem copyItemsTrace (fill : Bool) (r : RawInstance)
    (a index payload reversed : List Bool) :
    (advance machine.step)^[(rawInstanceBits r).length]
      (some (cfg (some .items) fill (rawInstanceBits r ++ a) [] [] index payload reversed [])) =
      some (cfg (some .dispatch) fill a [] [] index payload
        ((rawInstanceBits r).reverse ++ reversed) []) := by
  induction r generalizing reversed with
  | nil =>
      simpa [rawInstanceBits, listBits, advance] using!
        copyFlagStep .numerator .dispatch .items rfl fill false a index payload reversed
  | cons q r ih =>
      have first := copyFlagStep .numerator .dispatch .items rfl fill true
        (natBits q.1 ++ (natBits q.2 ++ (rawInstanceBits r ++ a))) index payload reversed
      have second := copyNameTrace .numerator .numeratorDigit .denominator rfl rfl fill q.1.bits
        (natBits q.2 ++ (rawInstanceBits r ++ a)) index payload (true :: reversed)
      have third := copyNameTrace .denominator .denominatorDigit .items rfl rfl fill q.2.bits
        (rawInstanceBits r ++ a) index payload ((natBits q.1).reverse ++ true :: reversed)
      simp only [↓reduceIte] at first
      have last := ih ((natBits q.2).reverse ++ ((natBits q.1).reverse ++ true :: reversed))
      simp only [natBits, BinPackingCompleteness.BinaryEncoding.nameBits] at first second third last
      have full := joinTrace (joinTrace (joinTrace
        (oneStepTrace first) second) third) last
      have clock : 1 + (BinPackingCompleteness.BinaryEncoding.frame q.1.bits).length +
          (BinPackingCompleteness.BinaryEncoding.frame q.2.bits).length +
          (rawInstanceBits r).length = (rawInstanceBits (q :: r)).length := by
        simp only [rawInstanceBits, listBits, pairBits, natBits,
          BinPackingCompleteness.BinaryEncoding.nameBits, List.length_cons, List.length_append]
        omega
      rw [clock] at full
      simpa only [rawInstanceBits, listBits, pairBits, natBits,
        BinPackingCompleteness.BinaryEncoding.nameBits, List.cons_append,
        List.reverse_cons, List.reverse_append, List.append_assoc,
        List.singleton_append, List.nil_append] using full

theorem dispatchStep (fill : Bool) (word index payload reversed : List Bool) :
    machine.step (cfg (some .dispatch) fill word [] [] index payload reversed []) =
      some (cfg (some (if fill then .replace (.entry true) else .fixed)) fill
        word [] [] index payload reversed []) := by
  change some (TM2.stepAux (code .dispatch) _ _) = _
  cases fill <;> simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem copyFixedTrace (word index payload reversed : List Bool) :
    (advance machine.step)^[word.length + 1]
      (some (cfg (some .fixed) false word [] [] index payload reversed [])) =
      some (cfg (some .reverse) false [] [] [] index payload (word.reverse ++ reversed) []) := by
  have h := transferAt_fromTapes (Γ := fun _ : Tape => Bool) .input .reversed (by decide)
    id false .fixed (some .reverse) code rfl
    (tapes word [] [] index payload reversed []) false none
  simpa only [cfg, transferNext, tapes_input, tapes_reversed, tapesAt,
    update_input, update_reversed, List.map_id_fun, id_eq] using! h

theorem replaceTapes_eq (source index payload reversed : List Bool) :
    SearchFixedReplaceMachine.tapes replacePlace (tapes [] [] [] [] [] [] [])
      (SearchFixedReplaceMachine.words source index payload reversed) =
        tapes source [] [] index payload reversed [] := by
  funext k
  cases k <;> rfl

theorem replaceFixedTrace (fixed : List (Option Nat)) (index value : Nat)
    (reversed : List Bool) :
    (advance machine.step)^[(fixedBits fixed).length + (index + 1) + (natBits value).length]
      (some (cfg (some (.replace (.entry true))) true (fixedBits fixed) [] []
        (encodeWord index) (natBits value) reversed [])) =
      some (cfg (some .reverse) true [] [] [] [] []
        ((fixedBits (fixed.set index (some value))).reverse ++ reversed) []) := by
  have h := SearchFixedReplaceMachine.replaceTrace replacePlace replacePlace_injective
    Label.replace (some .reverse) code (fun _ => rfl)
    (tapes [] [] [] [] [] [] []) true fixed index value [] [] [] reversed
  rw [actualStep] at h
  simpa only [SearchFixedReplaceMachine.configuration, replaceTapes_eq,
    List.append_nil, cfg] using! h

theorem reverseTrace (fill : Bool) (word index payload reversed : List Bool) :
    (advance machine.step)^[reversed.length + 1]
      (some (cfg (some .reverse) fill word [] [] index payload reversed [])) =
      some (cfg none fill word [] [] index payload [] reversed.reverse) := by
  have h := transferAt_fromTapes (Γ := fun _ : Tape => Bool) .reversed .output (by decide)
    id false .reverse none code rfl (tapes word [] [] index payload reversed []) fill none
  simpa only [cfg, transferNext, tapes_reversed, tapes_output, tapesAt,
    update_reversed, update_output, List.map_id_fun, id_eq, List.append_nil] using! h

def bodyBits (s : State) : List Bool :=
  encodeWord s.bins ++ (encodeWord s.item ++ (encodeWord s.label ++
    (rawInstanceBits s.items ++ fixedBits s.fixed)))

def selectedFixed (fill : Bool) (s : State) : List (Option Nat) :=
  if fill then s.fixed.set s.item (some s.label) else s.fixed

def queryBits (fill : Bool) (s : State) : List Bool :=
  extensionBits s.bins s.items (selectedFixed fill s)

def prefixSteps (s : State) : Nat :=
  UnaryToBinaryMachine.steps s.bins 0 + (s.bins.bits.length + 1) + 1 +
    (s.item + 1) + UnaryToBinaryMachine.steps s.label 0 + (s.label.bits.length + 1) +
    ((natBits s.label).length + 1) + (rawInstanceBits s.items).length

theorem prefixTrace (fill : Bool) (s : State) (saved : List Bool) :
    (advance machine.step)^[prefixSteps s]
      (some (cfg (some (.convertBins .scan)) fill (bodyBits s) [] [] [] [] saved [])) =
      some (cfg (some .dispatch) fill (fixedBits s.fixed) [] []
        (encodeWord s.item) (natBits s.label)
        ((rawInstanceBits s.items).reverse ++ (natBits s.bins).reverse ++ saved) []) := by
  let rest := encodeWord s.item ++ (encodeWord s.label ++
    (rawInstanceBits s.items ++ fixedBits s.fixed))
  let tail := rawInstanceBits s.items ++ fixedBits s.fixed
  let header := (natBits s.bins).reverse ++ saved
  have first := convertBinsTrace fill s.bins rest saved
  have second := emitBinsTrace fill s.bins rest saved
  have third := seedIndexStep fill rest header
  have fourth := indexTrace fill s.item 0 (encodeWord s.label ++ tail) header
  simp only [Nat.zero_add, encodeWord, List.replicate_zero, List.nil_append] at fourth
  have fifth := convertLabelTrace fill s.label tail (encodeWord s.item) header
  have sixth := emitLabelTrace fill s.label tail (encodeWord s.item) header
  have seventh := restoreLabelTrace fill s.label tail (encodeWord s.item) header
  have eighth := copyItemsTrace fill s.items (fixedBits s.fixed)
    (encodeWord s.item) (natBits s.label) header
  have full := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace first second)
      (oneStepTrace third)) fourth) fifth) sixth) seventh) eighth
  simpa only [prefixSteps, bodyBits, rest, tail, header, List.append_assoc,
    Nat.add_assoc] using full

def suffixSteps (fill : Bool) (s : State) : Nat :=
  1 + if fill then (fixedBits s.fixed).length + (s.item + 1) + (natBits s.label).length
    else (fixedBits s.fixed).length + 1

theorem suffixTrace (fill : Bool) (s : State) (acc : List Bool) :
    (advance machine.step)^[suffixSteps fill s]
      (some (cfg (some .dispatch) fill (fixedBits s.fixed) [] []
        (encodeWord s.item) (natBits s.label) acc [])) =
      some (cfg (some .reverse) fill [] [] []
        (if fill then [] else encodeWord s.item) (if fill then [] else natBits s.label)
        ((fixedBits (selectedFixed fill s)).reverse ++ acc) []) := by
  cases fill with
  | false =>
      have first := dispatchStep false (fixedBits s.fixed)
        (encodeWord s.item) (natBits s.label) acc
      have second := copyFixedTrace (fixedBits s.fixed)
        (encodeWord s.item) (natBits s.label) acc
      simp only [Bool.false_eq_true, ↓reduceIte] at first
      have full := joinTrace (oneStepTrace first) second
      simpa only [suffixSteps, selectedFixed, Bool.false_eq_true, ↓reduceIte] using full
  | true =>
      have first := dispatchStep true (fixedBits s.fixed)
        (encodeWord s.item) (natBits s.label) acc
      have second := replaceFixedTrace s.fixed s.item s.label acc
      simp only [↓reduceIte] at first
      have full := joinTrace (oneStepTrace first) second
      simpa only [suffixSteps, selectedFixed, Bool.true_eq, ↓reduceIte] using full

def activeBits (fill : Bool) (s : State) : List Bool :=
  BinPackingCompleteness.BinaryEncoding.frame (stateBits s) ++ queryBits fill s

def activeSteps (fill : Bool) (s : State) : Nat :=
  prefixSteps s + suffixSteps fill s + (activeBits fill s).length + 1

theorem activeTrace (fill : Bool) (s : State) :
    (advance machine.step)^[activeSteps fill s]
      (some (cfg (some (.convertBins .scan)) fill (bodyBits s) [] [] [] []
        ((BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).reverse) [])) =
      some (cfg none fill [] [] []
        (if fill then [] else encodeWord s.item) (if fill then [] else natBits s.label)
        [] (activeBits fill s)) := by
  let saved := (BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).reverse
  let header := (rawInstanceBits s.items).reverse ++ (natBits s.bins).reverse ++ saved
  have first := prefixTrace fill s saved
  have second := suffixTrace fill s header
  have third := reverseTrace fill []
    (if fill then [] else encodeWord s.item) (if fill then [] else natBits s.label)
    ((fixedBits (selectedFixed fill s)).reverse ++ header)
  have full := joinTrace (joinTrace first second) third
  simpa only [activeSteps, activeBits, queryBits, extensionBits, fixedBits,
    saved, header, List.reverse_append, List.reverse_reverse, List.length_reverse,
    List.length_append, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using full

def initialSteps (s : State) : Nat := 2 * ((stateBits s).length + 1) + ((stateBits s).length + 1)

theorem initialTrace (s : State) :
    (advance machine.step)^[initialSteps s]
      (some (cfg (some .save) false (stateBits s) [] [] [] [] [] [])) =
      some (cfg (some .phase) false (stateBits s) [] [] [] []
        ((BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).reverse) []) :=
  joinTrace (saveTrace (stateBits s)) (frameSavedTrace (stateBits s))

noncomputable def rawTime : Polynomial Nat := 100 * (Polynomial.X + 1) ^ 2

theorem activeSteps_le (fill : Bool) (s : State) :
    initialSteps s + 1 + activeSteps fill s ≤ rawTime.eval (stateBits s).length := by
  have hb := UnaryToBinaryMachine.steps_le s.bins 0
  have hl := UnaryToBinaryMachine.steps_le s.label 0
  have hbs : s.bins.size ≤ s.bins := Nat.size_le.mpr s.bins.lt_two_pow_self
  have hls : s.label.size ≤ s.label := Nat.size_le.mpr s.label.lt_two_pow_self
  have hfixed := fixedBits_set_length_le s.fixed s.item s.label
  have hselected : (fixedBits (selectedFixed fill s)).length ≤
      (fixedBits s.fixed).length + 2 * s.label + 2 := by
    cases fill <;> simp only [selectedFixed, Bool.false_eq_true, ↓reduceIte]
    · omega
    · exact hfixed
  have hlen := stateBits_length s
  have hbN : s.bins ≤ (stateBits s).length := by omega
  have hlN : s.label ≤ (stateBits s).length := by omega
  have hbSq := Nat.mul_le_mul hbN hbN
  have hlSq := Nat.mul_le_mul hlN hlN
  simp only [Nat.zero_add] at hb hl
  simp only [fixedBits] at hselected hfixed hlen
  simp only [initialSteps, activeSteps, prefixSteps, suffixSteps, activeBits, queryBits,
    extensionBits, fixedBits, List.length_append, BinPackingCompleteness.BinaryEncoding.frame_length,
    natBits_length, Nat.size_eq_bits_len, rawTime, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  cases fill <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> nlinarith

theorem inactiveSteps_le (s : State) :
    initialSteps s + 1 + ((BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).length + 1) ≤
      rawTime.eval (stateBits s).length := by
  simp only [initialSteps, rawTime, BinPackingCompleteness.BinaryEncoding.frame_length,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  nlinarith [Nat.zero_le (stateBits s).length]

theorem init_eq (input : List Bool) :
    initList machine input = cfg (some .save) false input [] [] [] [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  cases k <;> rfl

theorem savedFrame_eq (word : List Bool) :
    MachineKeepDecision.frame word = BinPackingCompleteness.BinaryEncoding.frame word := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
      simp only [MachineKeepDecision.frame, BinPackingCompleteness.BinaryEncoding.frame, ih]

private def activeRun (fill : Bool) (s : State)
    (hphase : phaseBits s.phase = [false, fill]) (hquery : query s = queryBits fill s) :
    MachineCanonicalOutput.TerminalRun program (stateBits s)
      (MachineKeepDecision.typedInputBits stateBits (prepare s))
      (rawTime.eval (stateBits s).length) := by
  let saved := (BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).reverse
  have middle : (advance machine.step)^[1]
      (some (cfg (some .phase) false (stateBits s) [] [] [] [] saved [])) =
      some (cfg (some (.convertBins .scan)) fill (bodyBits s) [] [] [] [] saved []) := by
    simpa only [stateBits, hphase, bodyBits, List.cons_append, List.nil_append,
      List.append_assoc, Function.iterate_one, advance_some] using
      phaseActive fill (bodyBits s) saved
  have full := joinTrace (joinTrace (initialTrace s) middle) (activeTrace fill s)
  refine {
    state := (fill, none)
    tapes := tapes [] [] []
      (if fill then [] else encodeWord s.item) (if fill then [] else natBits s.label)
      [] (activeBits fill s)
    execution := {
      steps := initialSteps s + 1 + activeSteps fill s
      evals_in_steps := ?_
      steps_le_m := activeSteps_le fill s }
    output_eq := ?_ }
  · change (advance machine.step)^[initialSteps s + 1 + activeSteps fill s]
      (some (initList machine (stateBits s))) =
        some (cfg none fill [] [] []
          (if fill then [] else encodeWord s.item) (if fill then [] else natBits s.label)
          [] (activeBits fill s))
    simpa only [init_eq] using full
  · change activeBits fill s = MachineKeepDecision.typedInputBits stateBits (prepare s)
    simp only [activeBits, MachineKeepDecision.typedInputBits,
      MachineKeepDecision.inputBits, prepare, hquery, savedFrame_eq]

private def inactiveRun (bit : Bool) (s : State)
    (hphase : phaseBits s.phase = [true, bit]) (hquery : query s = []) :
    MachineCanonicalOutput.TerminalRun program (stateBits s)
      (MachineKeepDecision.typedInputBits stateBits (prepare s))
      (rawTime.eval (stateBits s).length) := by
  let saved := (BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).reverse
  have middle : (advance machine.step)^[1]
      (some (cfg (some .phase) false (stateBits s) [] [] [] [] saved [])) =
      some (cfg (some .reverse) false (bit :: bodyBits s) [] [] [] [] saved []) := by
    simpa only [stateBits, hphase, bodyBits, List.cons_append, List.nil_append,
      List.append_assoc, Function.iterate_one, advance_some] using
      phaseInactive bit (bodyBits s) saved
  have last := reverseTrace false (bit :: bodyBits s) [] [] saved
  simp only [saved, List.length_reverse, List.reverse_reverse] at last
  have full := joinTrace (joinTrace (initialTrace s) middle) last
  refine {
    state := (false, none)
    tapes := tapes (bit :: bodyBits s) [] [] [] [] []
      (BinPackingCompleteness.BinaryEncoding.frame (stateBits s))
    execution := {
      steps := initialSteps s + 1 +
        ((BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).length + 1)
      evals_in_steps := ?_
      steps_le_m := inactiveSteps_le s }
    output_eq := ?_ }
  · change (advance machine.step)^[initialSteps s + 1 +
        ((BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).length + 1)]
      (some (initList machine (stateBits s))) =
        some (cfg none false (bit :: bodyBits s) [] [] [] [] []
          (BinPackingCompleteness.BinaryEncoding.frame (stateBits s)))
    simpa only [init_eq] using full
  · change BinPackingCompleteness.BinaryEncoding.frame (stateBits s) =
      MachineKeepDecision.typedInputBits stateBits (prepare s)
    simp only [MachineKeepDecision.typedInputBits,
      MachineKeepDecision.inputBits, prepare, hquery, savedFrame_eq, List.append_nil]

def rawRun (s : State) :
    MachineCanonicalOutput.TerminalRun program (stateBits s)
      (MachineKeepDecision.typedInputBits stateBits (prepare s))
      (rawTime.eval (stateBits s).length) := by
  cases hp : s.phase with
  | find =>
      exact activeRun false s (by simp [hp, phaseBits])
        (by simp [query, hp, queryBits, selectedFixed])
  | fill =>
      exact activeRun true s (by simp [hp, phaseBits])
        (by simp [query, hp, queryBits, selectedFixed])
  | done => exact inactiveRun false s (by simp [hp, phaseBits]) (by simp [query, hp])
  | invalid => exact inactiveRun true s (by simp [hp, phaseBits]) (by simp [query, hp])

def cleanupTapes : List Tape := [.input, .binary, .scratch, .index, .payload, .reversed]

theorem cleanup_complete (k : Tape) : k ∈ cleanupTapes ↔ k ≠ program.output := by
  cases k <;> simp [cleanupTapes, program]

noncomputable def computation :
    TM2ComputableInPolyTime stateBits (MachineKeepDecision.typedInputBits stateBits) prepare :=
  MachineCanonicalOutput.computableInPolyTime program cleanupTapes cleanup_complete
    stateBits (MachineKeepDecision.typedInputBits stateBits) prepare rawTime rawRun

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet program cleanupTapes
    cleanup_complete stateBits (MachineKeepDecision.typedInputBits stateBits) prepare rawTime rawRun

end BinPackingGap.SearchPrepareMachine

end OAI
