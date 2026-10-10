import OAI.Computability.BinPacking.Arithmetic.BinaryTallyMachine
import OAI.Computability.BinPacking.Machines.FrameEmitMachine
import OAI.Computability.BinPacking.Search.SearchFixedReplaceMachine

namespace OAI

namespace BinPackingGap.SearchUpdateMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open SearchSemantics SearchEncoding BinaryEncoding

inductive Tape
  | input | index | compare | binary | scratch | payload | reversed | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .index, .compare, .binary, .scratch,
  .payload, .reversed, .output]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | start | copyRest | reverse | finish
  | findBins | skipItem | skipLabel | zeroControls
  | fillNoBins | fillNoItem | incrementLabel
  | fillYesBins | startItem | fillYesItem
  | convert (label : UnaryToBinaryMachine.Label)
  | frame | restorePayload | zeroLabel
  | items | numerator | numeratorDigit | denominator | denominatorDigit
  | replace (label : SearchFixedReplaceMachine.Label)
  deriving DecidableEq, Fintype

structure Ambient where
  phaseHigh : Bool
  phaseLow : Bool
  flag : Bool
  deriving DecidableEq, Fintype

abbrev Register := Ambient × Option Bool
abbrev Tapes := Tape → List Bool

def ambient (phase : Phase) (flag : Bool := false) : Ambient :=
  match phase with
  | .find => ⟨false, false, flag⟩
  | .fill => ⟨false, true, flag⟩
  | .done => ⟨true, false, flag⟩
  | .invalid => ⟨true, true, flag⟩

def empty : Tapes := fun _ => []

def put (tapes : Tapes) (tape : Tape) (word : List Bool) : Tapes :=
  Function.update tapes tape word

def replacePlace : SearchFixedReplaceMachine.Slot → Tape
  | .source => .input
  | .index => .index
  | .payload => .payload
  | .reversed => .reversed

theorem replacePlace_injective : Function.Injective replacePlace := by
  intro a b h; cases a <;> cases b <;> simp_all [replacePlace]

def go (next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .load (fun state => (state.1, none)) (.goto (fun _ => next))

def choose (phase : Phase) (next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .load (fun _ => (ambient phase, none)) (.goto (fun _ => next))

def copyBit (zero one : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .pop .input (fun state head => (state.1, head))
    (.push .reversed (fun state => state.2.getD false)
      (.branch (fun state => state.2.getD false) (go one) (go zero)))

def copyDigit (next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .pop .input (fun state head => (state.1, head))
    (.push .reversed (fun state => state.2.getD false) (go next))

def skipUnary (again next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .pop .input (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false) (go again) (go next))

def code : Label → TM2.Stmt (fun _ : Tape => Bool) Label Register
  | .start =>
      .pop .input (fun state head => ({state.1 with flag := head.getD false}, none))
        (.pop .input (fun state head => ({state.1 with phaseHigh := head.getD false}, none))
          (.pop .input (fun state head => ({state.1 with phaseLow := head.getD false}, none))
            (.branch (fun state => state.1.phaseHigh)
              (go .copyRest)
              (.branch (fun state => state.1.phaseLow)
                (.branch (fun state => state.1.flag)
                  (choose .fill .fillYesBins) (choose .fill .fillNoBins))
                (.branch (fun state => state.1.flag)
                  (choose .fill .findBins)
                  (.push .reversed (fun _ => true) (choose .find .copyRest)))))))
  | .copyRest => loopAt .input .reversed id false .copyRest (some .reverse)
  | .reverse => loopAt .reversed .output id false .reverse (some .finish)
  | .finish => .push .output (fun state => state.1.phaseLow)
      (.push .output (fun state => state.1.phaseHigh)
        (.load (fun state => (state.1, none)) .halt))
  | .findBins => copyBit .skipItem .findBins
  | .skipItem => skipUnary .skipItem .skipLabel
  | .skipLabel => skipUnary .skipLabel .zeroControls
  | .zeroControls => .push .reversed (fun _ => false)
      (.push .reversed (fun _ => false) (go .copyRest))
  | .fillNoBins => copyBit .fillNoItem .fillNoBins
  | .fillNoItem => copyBit .incrementLabel .fillNoItem
  | .incrementLabel => .push .reversed (fun _ => true) (go .copyRest)
  | .fillYesBins => copyBit .startItem .fillYesBins
  | .startItem => .push .reversed (fun _ => true)
      (.push .index (fun _ => false) (.push .compare (fun _ => false) (go .fillYesItem)))
  | .fillYesItem => .pop .input (fun state head => (state.1, head))
      (.push .reversed (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false)
          (.push .index (fun _ => true) (.push .compare (fun _ => true) (go .fillYesItem)))
          (.push .compare (fun _ => true) (go (.convert .scan)))))
  | .convert label => UnaryToBinaryMachine.instruction .input .binary .scratch
      Label.convert (some .frame) label
  | .frame => FrameEmitMachine.instruction .binary .scratch .frame (some .restorePayload)
  | .restorePayload => loopAt .scratch .payload id false .restorePayload (some .zeroLabel)
  | .zeroLabel => .push .reversed (fun _ => false) (go .items)
  | .items => .pop .input (fun state head => (state.1, head))
      (.push .reversed (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false)
          (.pop .compare (fun state head =>
            ({state.1 with flag := state.1.flag || !(head.getD false)}, none))
            (go .numerator))
          (.peek .compare (fun state head =>
            (ambient (if !state.1.flag && !(head.getD false) then .done else .fill), none))
            (go (.replace (.entry true))))))
  | .numerator => copyBit .denominator .numeratorDigit
  | .numeratorDigit => copyDigit .numerator
  | .denominator => copyBit .items .denominatorDigit
  | .denominatorDigit => copyDigit .denominator
  | .replace label => SearchFixedReplaceMachine.instruction replacePlace
      Label.replace (some .reverse) label

def program : MachineCanonicalOutput.Program Tape Label Register where
  input := .input
  output := .output
  main := .start
  initial := (ambient .find, none)
  code := code

abbrev machine := MachineCanonicalOutput.sourceMachine program

private theorem machine_step : machine.step = TM2.step code := rfl

def cfg (label : Option Label) (phase : Ambient) (tapes : Tapes)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, (phase, register), tapes⟩

def io (base : Tapes) (input reversed : List Bool) : Tapes :=
  put (put base .input input) .reversed reversed

@[simp] theorem io_input (base : Tapes) (input reversed : List Bool) :
    io base input reversed .input = input := by simp [io, put]

@[simp] theorem io_reversed (base : Tapes) (input reversed : List Bool) :
    io base input reversed .reversed = reversed := by simp [io, put]

theorem update_io_input (base : Tapes) (input reversed next : List Bool) :
    Function.update (io base input reversed) .input next = io base next reversed := by
  funext k; cases k <;> simp [io, put]

theorem update_io_reversed (base : Tapes) (input reversed next : List Bool) :
    Function.update (io base input reversed) .reversed next = io base input next := by
  simp [io, put]

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

private theorem oneStepTrace {a b : machine.Cfg} (h : machine.step a = some b) :
    (advance machine.step)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

theorem copyBitStep (current zero one : Label) (atLabel : code current = copyBit zero one)
    (bit : Bool) (phase : Ambient) (base : Tapes) (input reversed : List Bool) :
    machine.step (cfg (some current) phase (io base (bit :: input) reversed)) =
      some (cfg (some (if bit then one else zero)) phase
        (io base input (bit :: reversed))) := by
  change some (TM2.stepAux (code current) _ _) = _
  rw [atLabel]
  cases bit <;> simp [copyBit, go, TM2.stepAux, cfg,
    update_io_input, update_io_reversed]
  all_goals rfl

theorem copyDigitStep (current next : Label) (atLabel : code current = copyDigit next)
    (bit : Bool) (phase : Ambient) (base : Tapes) (input reversed : List Bool) :
    machine.step (cfg (some current) phase (io base (bit :: input) reversed)) =
      some (cfg (some next) phase (io base input (bit :: reversed))) := by
  change some (TM2.stepAux (code current) _ _) = _
  rw [atLabel]
  simp [copyDigit, go, TM2.stepAux, cfg, update_io_input, update_io_reversed]
  all_goals rfl

theorem unaryCopyTrace (current next : Label) (atLabel : code current = copyBit next current)
    (n : Nat) (phase : Ambient) (base : Tapes) (input reversed : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some current) phase (io base (encodeWord n ++ input) reversed))) =
      some (cfg (some next) phase (io base input ((encodeWord n).reverse ++ reversed))) := by
  induction n generalizing reversed with
  | zero =>
      simpa [encodeWord, advance] using! copyBitStep current next current atLabel
        false phase base input reversed
  | succ n ih =>
      have first := copyBitStep current next current atLabel true phase base
        (encodeWord n ++ input) reversed
      have second := ih (true :: reversed)
      have full := joinTrace (oneStepTrace first) second
      simpa [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem unarySkipStep (current next : Label) (atLabel : code current = skipUnary current next)
    (bit : Bool) (phase : Ambient) (base : Tapes) (input reversed : List Bool) :
    machine.step (cfg (some current) phase (io base (bit :: input) reversed)) =
      some (cfg (some (if bit then current else next)) phase (io base input reversed)) := by
  change some (TM2.stepAux (code current) _ _) = _
  rw [atLabel]
  cases bit <;> simp [skipUnary, go, TM2.stepAux, cfg, update_io_input]
  all_goals rfl

theorem unarySkipTrace (current next : Label) (atLabel : code current = skipUnary current next)
    (n : Nat) (phase : Ambient) (base : Tapes) (input reversed : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some current) phase (io base (encodeWord n ++ input) reversed))) =
      some (cfg (some next) phase (io base input reversed)) := by
  induction n with
  | zero =>
      simpa [encodeWord, advance] using! unarySkipStep current next atLabel
        false phase base input reversed
  | succ n ih =>
      have first := unarySkipStep current next atLabel true phase base
        (encodeWord n ++ input) reversed
      have full := joinTrace (oneStepTrace first) ih
      simpa [encodeWord, List.replicate_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

theorem nameCopyTrace (flag digit next : Label)
    (flagCode : code flag = copyBit next digit) (digitCode : code digit = copyDigit flag)
    (bits : List Bool) (phase : Ambient) (base : Tapes) (input reversed : List Bool) :
    (advance machine.step)^[(BinPackingCompleteness.BinaryEncoding.frame bits).length]
      (some (cfg (some flag) phase
        (io base (BinPackingCompleteness.BinaryEncoding.frame bits ++ input) reversed))) =
      some (cfg (some next) phase
        (io base input ((BinPackingCompleteness.BinaryEncoding.frame bits).reverse ++ reversed))) := by
  induction bits generalizing reversed with
  | nil =>
      simpa [BinPackingCompleteness.BinaryEncoding.frame, advance] using!
        copyBitStep flag next digit flagCode false phase base input reversed
  | cons bit bits ih =>
      have first := copyBitStep flag next digit flagCode true phase base
        (bit :: (BinPackingCompleteness.BinaryEncoding.frame bits ++ input)) reversed
      have second := copyDigitStep digit flag digitCode bit phase base
        (BinPackingCompleteness.BinaryEncoding.frame bits ++ input) (true :: reversed)
      have third := ih (bit :: true :: reversed)
      have full := joinTrace (joinTrace
        (oneStepTrace first) (oneStepTrace second)) third
      have clock : 1 + 1 + (BinPackingCompleteness.BinaryEncoding.frame bits).length =
          (BinPackingCompleteness.BinaryEncoding.frame (bit :: bits)).length := by
        simp only [BinPackingCompleteness.BinaryEncoding.frame, List.length_cons]
        omega
      rw [clock] at full
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
        List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using full

def decrement (counter : List Bool × Bool) : List Bool × Bool :=
  (counter.1.tail, counter.2 || !(counter.1.head?.getD false))

def counterAfter : Nat → (List Bool × Bool) → List Bool × Bool
  | 0, counter => counter
  | n + 1, counter => counterAfter n (decrement counter)

def countedPhase (counter : List Bool × Bool) : Phase :=
  if !counter.2 && !(counter.1.head?.getD false) then .done else .fill

@[simp] theorem counterAfter_empty (n : Nat) :
    counterAfter n ([], true) = ([], true) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [counterAfter, decrement] using ih

theorem countedPhase_counterAfter (m n : Nat) :
    countedPhase (counterAfter m (encodeWord n, false)) =
      if m = n then .done else .fill := by
  induction m generalizing n with
  | zero => cases n <;> simp [counterAfter, countedPhase, encodeWord, List.replicate_succ]
  | succ m ih =>
      cases n with
      | zero => simp [counterAfter, decrement, encodeWord, countedPhase]
      | succ n => simpa [counterAfter, decrement, encodeWord, List.replicate_succ] using ih n

def countIO (base : Tapes) (counter : List Bool × Bool)
    (input reversed : List Bool) : Tapes := io (put base .compare counter.1) input reversed

theorem itemsStep_nil (base : Tapes) (counter : List Bool × Bool)
    (input reversed : List Bool) :
    machine.step (cfg (some .items) (ambient .fill counter.2)
      (countIO base counter (false :: input) reversed)) =
      some (cfg (some (.replace (.entry true))) (ambient (countedPhase counter))
        (countIO base counter input (false :: reversed))) := by
  change some (TM2.stepAux (code .items) _ _) = _
  simp [code, go, TM2.stepAux, cfg, countIO, countedPhase, ambient, io, put]
  congr 1
  congr 1
  funext tape; cases tape <;> simp

theorem itemsStep_cons (base : Tapes) (counter : List Bool × Bool)
    (input reversed : List Bool) :
    machine.step (cfg (some .items) (ambient .fill counter.2)
      (countIO base counter (true :: input) reversed)) =
      some (cfg (some .numerator) (ambient .fill (decrement counter).2)
        (countIO base (decrement counter) input (true :: reversed))) := by
  change some (TM2.stepAux (code .items) _ _) = _
  simp [code, go, TM2.stepAux, cfg, countIO, decrement, ambient, io, put]
  congr 1
  congr 1
  funext tape; cases tape <;> simp

theorem itemsTrace (items : RawInstance) (base : Tapes) (counter : List Bool × Bool)
    (input reversed : List Bool) :
    (advance machine.step)^[(rawInstanceBits items).length]
      (some (cfg (some .items) (ambient .fill counter.2)
        (countIO base counter (rawInstanceBits items ++ input) reversed))) =
      some (cfg (some (.replace (.entry true)))
        (ambient (countedPhase (counterAfter items.length counter)))
        (countIO base (counterAfter items.length counter) input
          ((rawInstanceBits items).reverse ++ reversed))) := by
  induction items generalizing counter reversed with
  | nil =>
      simpa [rawInstanceBits, listBits, counterAfter, advance] using!
        itemsStep_nil base counter input reversed
  | cons item items ih =>
      let rest := rawInstanceBits items ++ input
      let nextCounter := decrement counter
      have first := itemsStep_cons base counter
        (natBits item.1 ++ natBits item.2 ++ rest) reversed
      have second := nameCopyTrace .numerator .numeratorDigit .denominator rfl rfl
        item.1.bits (ambient .fill nextCounter.2) (put base .compare nextCounter.1)
        (natBits item.2 ++ rest) (true :: reversed)
      have third := nameCopyTrace .denominator .denominatorDigit .items rfl rfl
        item.2.bits (ambient .fill nextCounter.2) (put base .compare nextCounter.1)
        rest ((natBits item.1).reverse ++ true :: reversed)
      have fourth := ih nextCounter
        ((natBits item.2).reverse ++ (natBits item.1).reverse ++ true :: reversed)
      simp only [rest, countIO, natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
        List.append_assoc] at first second third fourth
      have full := joinTrace (joinTrace (joinTrace
        (oneStepTrace first) second) third) fourth
      have clock : 1 + (BinPackingCompleteness.BinaryEncoding.frame item.1.bits).length +
          (BinPackingCompleteness.BinaryEncoding.frame item.2.bits).length +
          (rawInstanceBits items).length = (rawInstanceBits (item :: items)).length := by
        simp only [rawInstanceBits, listBits, pairBits, natBits,
          BinPackingCompleteness.BinaryEncoding.nameBits, List.length_cons, List.length_append]
        omega
      rw [clock] at full
      simpa [rest, nextCounter, countIO, rawInstanceBits, listBits, pairBits,
        natBits, BinPackingCompleteness.BinaryEncoding.nameBits, counterAfter,
        List.reverse_cons, List.reverse_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def work (input index compare binary scratch payload reversed output : List Bool) : Tapes
  | .input => input
  | .index => index
  | .compare => compare
  | .binary => binary
  | .scratch => scratch
  | .payload => payload
  | .reversed => reversed
  | .output => output

@[simp] theorem put_work (a b c d e f g h x : List Bool) (tape : Tape) :
    Function.update (work a b c d e f g h) tape x =
      match tape with
      | .input => work x b c d e f g h
      | .index => work a x c d e f g h
      | .compare => work a b x d e f g h
      | .binary => work a b c x e f g h
      | .scratch => work a b c d x f g h
      | .payload => work a b c d e x g h
      | .reversed => work a b c d e f x h
      | .output => work a b c d e f g x := by
  funext k; cases tape <;> cases k <;> rfl

@[simp] theorem io_work (a b c d e f g h input reversed : List Bool) :
    io (work a b c d e f g h) input reversed = work input b c d e f reversed h := by
  simp only [io, put, put_work]

theorem transferTrace (source target : Tape) (distinct : source ≠ target)
    (current : Label) (next : Option Label)
    (atLabel : code current = loopAt source target id false current next)
    (phase : Ambient) (tapes : Tapes) :
    (advance machine.step)^[(tapes source).length + 1]
      (some (cfg (some current) phase tapes)) =
      some (cfg next phase
        (put (put tapes source []) target ((tapes source).reverse ++ tapes target))) := by
  have trace := transferAt_fromTapes source target distinct id false current next
    code atLabel tapes phase none
  have next_eq : nextAt target code = advance (TM2.step code) := by funext s; rfl
  rw [next_eq] at trace
  simpa only [machine_step, cfg, put, List.map_id_fun, id_eq, tapesAt] using! trace

theorem finishStep (phase : Ambient) (tapes : Tapes) :
    machine.step (cfg (some .finish) phase tapes) =
      some (cfg none phase
        (put tapes .output (phase.phaseHigh :: phase.phaseLow :: tapes .output))) := by
  change some (TM2.stepAux (code .finish) _ _) = _
  simp [code, TM2.stepAux, cfg, put]
  all_goals rfl

def phaseWord (phase : Ambient) : List Bool := [phase.phaseHigh, phase.phaseLow]

@[simp] theorem phaseWord_ambient (phase : Phase) (flag : Bool) :
    phaseWord (ambient phase flag) = phaseBits phase := by cases phase <;> rfl

theorem reverseFinishTrace (phase : Ambient) (a b c d e f reversed : List Bool) :
    (advance machine.step)^[reversed.length + 2]
      (some (cfg (some .reverse) phase (work a b c d e f reversed []))) =
      some (cfg none phase (work a b c d e f [] (phaseWord phase ++ reversed.reverse))) := by
  have first := transferTrace .reversed .output (by decide) .reverse (some .finish)
    rfl phase (work a b c d e f reversed [])
  simp only [work, put, put_work, List.append_nil] at first
  have second := finishStep phase (work a b c d e f [] reversed.reverse)
  simp only [work, put, put_work] at second
  have full := joinTrace first (oneStepTrace second)
  simpa [phaseWord, Nat.add_assoc] using full

theorem copyRestTrace (phase : Ambient) (input b c d e f reversed : List Bool) :
    (advance machine.step)^[2 * input.length + reversed.length + 3]
      (some (cfg (some .copyRest) phase (work input b c d e f reversed []))) =
      some (cfg none phase
        (work [] b c d e f [] (phaseWord phase ++ reversed.reverse ++ input))) := by
  have first := transferTrace .input .reversed (by decide) .copyRest (some .reverse)
    rfl phase (work input b c d e f reversed [])
  simp only [work, put, put_work] at first
  have second := reverseFinishTrace phase [] b c d e f (input.reverse ++ reversed)
  have full := joinTrace first second
  simpa [List.reverse_append, List.reverse_reverse, List.length_append, List.append_assoc,
    Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def bodyBits (s : State) : List Bool :=
  encodeWord s.bins ++ encodeWord s.item ++ encodeWord s.label ++
    rawInstanceBits s.items ++ fixedBits s.fixed

@[simp] theorem stateBits_eq (s : State) : stateBits s = phaseBits s.phase ++ bodyBits s := by
  simp [stateBits, bodyBits, List.append_assoc]

def initialTarget (phase : Phase) (answer : Bool) : Label × Ambient × List Bool :=
  match phase, answer with
  | .find, false => (.copyRest, ambient .find, [true])
  | .find, true => (.findBins, ambient .fill, [])
  | .fill, false => (.fillNoBins, ambient .fill, [])
  | .fill, true => (.fillYesBins, ambient .fill, [])
  | .done, answer => (.copyRest, ambient .done answer, [])
  | .invalid, answer => (.copyRest, ambient .invalid answer, [])

theorem startStep (phase : Phase) (answer : Bool) (body : List Bool) :
    machine.step (cfg (some .start) (ambient .find)
      (work (answer :: (phaseBits phase ++ body)) [] [] [] [] [] [] [])) =
      some (cfg (some (initialTarget phase answer).1) (initialTarget phase answer).2.1
        (work body [] [] [] [] [] (initialTarget phase answer).2.2 [])) := by
  change some (TM2.stepAux (code .start) _ _) = _
  cases phase <;> cases answer <;>
    simp [code, go, choose, TM2.stepAux, cfg, ambient, phaseBits,
      initialTarget, work]
  all_goals rfl

def itemWork (base : Tapes) (n : Nat) (input reversed : List Bool) : Tapes :=
  io (put (put base .index (encodeWord n)) .compare (encodeWord n)) input reversed

theorem itemStep_true (phase : Ambient) (base : Tapes) (n : Nat)
    (input reversed : List Bool) :
    machine.step (cfg (some .fillYesItem) phase (itemWork base n (true :: input) reversed)) =
      some (cfg (some .fillYesItem) phase (itemWork base (n + 1) input (true :: reversed))) := by
  change some (TM2.stepAux (code .fillYesItem) _ _) = _
  simp [code, go, TM2.stepAux, cfg, itemWork, io, put, encodeWord, List.replicate_succ]
  congr 1
  congr 1
  funext tape; cases tape <;> simp

theorem itemStep_false (phase : Ambient) (base : Tapes) (n : Nat)
    (input reversed : List Bool) :
    machine.step (cfg (some .fillYesItem) phase (itemWork base n (false :: input) reversed)) =
      some (cfg (some (.convert .scan)) phase
        (io (put (put base .index (encodeWord n)) .compare (encodeWord (n + 1)))
          input (false :: reversed))) := by
  change some (TM2.stepAux (code .fillYesItem) _ _) = _
  simp [code, go, TM2.stepAux, cfg, itemWork, io, put, encodeWord, List.replicate_succ]
  congr 1
  congr 1
  funext tape; cases tape <;> simp

theorem itemTrace (phase : Ambient) (base : Tapes) (n initial : Nat)
    (input reversed : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some .fillYesItem) phase
        (itemWork base initial (encodeWord n ++ input) reversed))) =
      some (cfg (some (.convert .scan)) phase
        (io (put (put base .index (encodeWord (initial + n)))
          .compare (encodeWord (initial + n + 1)))
          input ((encodeWord n).reverse ++ reversed))) := by
  induction n generalizing initial reversed with
  | zero =>
      simpa [encodeWord, advance] using! itemStep_false phase base initial input reversed
  | succ n ih =>
      have first := itemStep_true phase base initial (encodeWord n ++ input) reversed
      have second := ih (initial + 1) (true :: reversed)
      have full := joinTrace (oneStepTrace first) second
      simpa [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem startItemStep (phase : Ambient) (input reversed : List Bool) :
    machine.step (cfg (some .startItem) phase (work input [] [] [] [] [] reversed [])) =
      some (cfg (some .fillYesItem) phase (work input [false] [false] [] [] [] (true :: reversed) [])) := by
  change some (TM2.stepAux (code .startItem) _ _) = _
  simp [code, go, TM2.stepAux, cfg, put_work, work]
  all_goals rfl

theorem convertTrace (phase : Ambient) (n : Nat) (input index compare reversed : List Bool) :
    (advance machine.step)^[UnaryToBinaryMachine.steps n 0]
      (some (cfg (some (.convert .scan)) phase
        (work (encodeWord n ++ input) index compare [] [] [] reversed []))) =
      some (cfg (some .frame) phase (work input index compare n.bits [] [] reversed [])) := by
  have trace := UnaryToBinaryMachine.convertTrace (K := Tape) (A := Ambient)
    .input .binary .scratch (by decide) (by decide) (by decide)
    Label.convert (some .frame) code (fun _ => rfl)
    (work [] index compare [] [] [] reversed []) phase n 0 input
  have ht : ∀ a b c,
      UnaryToBinaryMachine.tapes .input .binary .scratch
        (work [] index compare [] [] [] reversed []) a b c =
      work a index compare b c [] reversed [] := by
    intro a b c; funext k; cases k <;> rfl
  simpa only [machine_step, UnaryToBinaryMachine.tapes, put_work, Nat.zero_add,
    Nat.zero_bits, cfg] using! trace

theorem frameTrace (phase : Ambient) (n : Nat) (input index compare reversed : List Bool) :
    (advance machine.step)^[n.bits.length + 1]
      (some (cfg (some .frame) phase (work input index compare n.bits [] [] reversed []))) =
      some (cfg (some .restorePayload) phase
        (work input index compare [] (natBits n).reverse [] reversed [])) := by
  have trace := FrameEmitMachine.trace (K := Tape) (A := Ambient) .binary .scratch
    (by decide) .frame (some .restorePayload) code rfl
    (work input index compare [] [] [] reversed []) phase n.bits []
  simpa only [machine_step, tapesAt, put_work, List.append_nil, natBits,
    BinPackingCompleteness.BinaryEncoding.nameBits, cfg] using! trace

theorem restorePayloadTrace (phase : Ambient) (n : Nat)
    (input index compare reversed : List Bool) :
    (advance machine.step)^[(natBits n).length + 1]
      (some (cfg (some .restorePayload) phase
        (work input index compare [] (natBits n).reverse [] reversed []))) =
      some (cfg (some .zeroLabel) phase
        (work input index compare [] [] (natBits n) reversed [])) := by
  have trace := transferTrace .scratch .payload (by decide) .restorePayload
    (some .zeroLabel) rfl phase
    (work input index compare [] (natBits n).reverse [] reversed [])
  simpa only [work, put, put_work, List.length_reverse, List.reverse_reverse,
    List.append_nil] using trace

theorem zeroLabelStep (phase : Ambient) (input index compare payload reversed : List Bool) :
    machine.step (cfg (some .zeroLabel) phase
      (work input index compare [] [] payload reversed [])) =
      some (cfg (some .items) phase
        (work input index compare [] [] payload (false :: reversed) [])) := by
  change some (TM2.stepAux (code .zeroLabel) _ _) = _
  simp [code, go, TM2.stepAux, cfg, put_work, work]
  all_goals rfl

theorem replaceTapes_eq (compare source index payload reversed : List Bool) :
    SearchFixedReplaceMachine.tapes replacePlace (work [] [] compare [] [] [] [] [])
      (SearchFixedReplaceMachine.words source index payload reversed) =
      work source index compare [] [] payload reversed [] := by
  funext k; cases k <;> rfl

theorem replaceTrace (phase : Ambient) (fixed : List (Option Nat)) (i value : Nat)
    (compare reversed : List Bool) :
    (advance machine.step)^[(fixedBits fixed).length + (i + 1) + (natBits value).length]
      (some (cfg (some (.replace (.entry true))) phase
        (work (fixedBits fixed) (encodeWord i) compare [] [] (natBits value) reversed []))) =
      some (cfg (some .reverse) phase (work [] [] compare [] [] []
        ((fixedBits (fixed.set i (some value))).reverse ++ reversed) [])) := by
  have trace := SearchFixedReplaceMachine.replaceTrace replacePlace replacePlace_injective
    Label.replace (some .reverse) code (fun _ => rfl)
    (work [] [] compare [] [] [] [] []) phase fixed i value [] [] [] reversed
  simpa only [machine_step, SearchFixedReplaceMachine.configuration, replaceTapes_eq,
    List.append_nil, cfg] using! trace

def fillHeader (s : State) : List Bool :=
  encodeWord s.bins ++ encodeWord (s.item + 1) ++ [false]

def newFixed (s : State) := s.fixed.set s.item (some s.label)

def fillBody (s : State) : List Bool :=
  fillHeader s ++ rawInstanceBits s.items ++ fixedBits (newFixed s)

def fillPhase (s : State) : Phase := if s.item + 1 = s.items.length then .done else .fill

def fillCounter (s : State) : List Bool × Bool :=
  counterAfter s.items.length (encodeWord (s.item + 1), false)

def fillPrefixSteps (s : State) : Nat :=
  (s.bins + 1) + 1 + (s.item + 1) + UnaryToBinaryMachine.steps s.label 0 +
    (s.label.bits.length + 1) + ((natBits s.label).length + 1) + 1 +
    (rawInstanceBits s.items).length

theorem fillPrefixTrace (s : State) :
    (advance machine.step)^[fillPrefixSteps s]
      (some (cfg (some .fillYesBins) (ambient .fill)
        (work (bodyBits s) [] [] [] [] [] [] []))) =
      some (cfg (some (.replace (.entry true))) (ambient (fillPhase s))
        (work (fixedBits s.fixed) (encodeWord s.item) (fillCounter s).1 [] []
          (natBits s.label) ((rawInstanceBits s.items).reverse ++ (fillHeader s).reverse) [])) := by
  let tail := rawInstanceBits s.items ++ fixedBits s.fixed
  let afterBins := encodeWord s.item ++ encodeWord s.label ++ tail
  let revBins := (encodeWord s.bins).reverse
  let revItem := (encodeWord s.item).reverse ++ true :: revBins
  have first := unaryCopyTrace .fillYesBins .startItem rfl s.bins (ambient .fill)
    (work [] [] [] [] [] [] [] []) afterBins []
  have second := startItemStep (ambient .fill) afterBins revBins
  have third := itemTrace (ambient .fill) (work [] [] [] [] [] [] [] [])
    s.item 0 (encodeWord s.label ++ tail) (true :: revBins)
  have fourth := convertTrace (ambient .fill) s.label tail
    (encodeWord s.item) (encodeWord (s.item + 1)) revItem
  have fifth := frameTrace (ambient .fill) s.label tail
    (encodeWord s.item) (encodeWord (s.item + 1)) revItem
  have sixth := restorePayloadTrace (ambient .fill) s.label tail
    (encodeWord s.item) (encodeWord (s.item + 1)) revItem
  have seventh := zeroLabelStep (ambient .fill) tail
    (encodeWord s.item) (encodeWord (s.item + 1)) (natBits s.label) revItem
  have eighth := itemsTrace s.items
    (work [] (encodeWord s.item) [] [] [] (natBits s.label) [] [])
    (encodeWord (s.item + 1), false) (fixedBits s.fixed) (false :: revItem)
  simp only [io_work, List.append_nil, afterBins, List.append_assoc] at first
  simp only [afterBins, List.append_assoc] at second
  simp only [itemWork, Nat.zero_add, put, put_work, io_work,
    show encodeWord 0 = [false] from rfl] at third
  simp only [countIO, put, put_work, io_work, countedPhase_counterAfter] at eighth
  have full := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace first (oneStepTrace second)) third)
      fourth) fifth) sixth) (oneStepTrace seventh)) eighth
  simpa [fillPrefixSteps, bodyBits, tail, afterBins, revBins, revItem, fillCounter,
    fillPhase, fillHeader, encodeWord, List.replicate_succ, List.reverse_cons,
    List.reverse_append, List.append_assoc, eq_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def fillSteps (s : State) : Nat :=
  fillPrefixSteps s + ((fixedBits s.fixed).length + (s.item + 1) + (natBits s.label).length) +
    ((fillBody s).length + 2)

theorem fillTrace (s : State) :
    (advance machine.step)^[fillSteps s]
      (some (cfg (some .fillYesBins) (ambient .fill)
        (work (bodyBits s) [] [] [] [] [] [] []))) =
      some (cfg none (ambient (fillPhase s))
        (work [] [] (fillCounter s).1 [] [] [] [] (phaseBits (fillPhase s) ++ fillBody s))) := by
  have first := fillPrefixTrace s
  have second := replaceTrace (ambient (fillPhase s)) s.fixed s.item s.label
    (fillCounter s).1 ((rawInstanceBits s.items).reverse ++ (fillHeader s).reverse)
  have third := reverseFinishTrace (ambient (fillPhase s)) [] [] (fillCounter s).1 [] [] []
    ((fixedBits (newFixed s)).reverse ++ (rawInstanceBits s.items).reverse ++ (fillHeader s).reverse)
  simp only [newFixed, List.append_assoc] at third
  have full := joinTrace (joinTrace first second) third
  simpa [fillSteps, fillBody, newFixed, List.reverse_append, List.reverse_reverse,
    List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem zeroControlsStep (phase : Ambient) (input reversed : List Bool) :
    machine.step (cfg (some .zeroControls) phase (work input [] [] [] [] [] reversed [])) =
      some (cfg (some .copyRest) phase (work input [] [] [] [] [] (false :: false :: reversed) [])) := by
  change some (TM2.stepAux (code .zeroControls) _ _) = _
  simp [code, go, TM2.stepAux, cfg, put_work, work]
  all_goals rfl

theorem incrementLabelStep (phase : Ambient) (input reversed : List Bool) :
    machine.step (cfg (some .incrementLabel) phase (work input [] [] [] [] [] reversed [])) =
      some (cfg (some .copyRest) phase (work input [] [] [] [] [] (true :: reversed) [])) := by
  change some (TM2.stepAux (code .incrementLabel) _ _) = _
  simp [code, go, TM2.stepAux, cfg, put_work, work]
  all_goals rfl

def findBody (s : State) : List Bool :=
  encodeWord s.bins ++ [false, false] ++ rawInstanceBits s.items ++ fixedBits s.fixed

def findSteps (s : State) : Nat :=
  (s.bins + 1) + (s.item + 1) + (s.label + 1) + 1 +
    (2 * (rawInstanceBits s.items ++ fixedBits s.fixed).length +
      (false :: false :: (encodeWord s.bins).reverse).length + 3)

theorem findTrace (s : State) :
    (advance machine.step)^[findSteps s]
      (some (cfg (some .findBins) (ambient .fill)
        (work (bodyBits s) [] [] [] [] [] [] []))) =
      some (cfg none (ambient .fill)
        (work [] [] [] [] [] [] [] (phaseBits .fill ++ findBody s))) := by
  let tail := rawInstanceBits s.items ++ fixedBits s.fixed
  let header := (encodeWord s.bins).reverse
  have first := unaryCopyTrace .findBins .skipItem rfl s.bins (ambient .fill)
    (work [] [] [] [] [] [] [] []) (encodeWord s.item ++ encodeWord s.label ++ tail) []
  have second := unarySkipTrace .skipItem .skipLabel rfl s.item (ambient .fill)
    (work [] [] [] [] [] [] [] []) (encodeWord s.label ++ tail) header
  have third := unarySkipTrace .skipLabel .zeroControls rfl s.label (ambient .fill)
    (work [] [] [] [] [] [] [] []) tail header
  have fourth := zeroControlsStep (ambient .fill) tail header
  have fifth := copyRestTrace (ambient .fill) tail [] [] [] [] [] (false :: false :: header)
  simp only [io_work, List.append_nil, List.append_assoc] at first second third
  have full := joinTrace (joinTrace (joinTrace (joinTrace first second) third)
    (oneStepTrace fourth)) fifth
  simpa [findSteps, bodyBits, findBody, tail, header, List.reverse_cons,
    List.reverse_reverse, List.append_assoc, Nat.add_assoc] using full

def fillNoBody (s : State) : List Bool :=
  encodeWord s.bins ++ encodeWord s.item ++ encodeWord (s.label + 1) ++
    rawInstanceBits s.items ++ fixedBits s.fixed

def fillNoSteps (s : State) : Nat :=
  (s.bins + 1) + (s.item + 1) + 1 +
    (2 * (encodeWord s.label ++ rawInstanceBits s.items ++ fixedBits s.fixed).length +
      (true :: (encodeWord s.item).reverse ++ (encodeWord s.bins).reverse).length + 3)

theorem fillNoTrace (s : State) :
    (advance machine.step)^[fillNoSteps s]
      (some (cfg (some .fillNoBins) (ambient .fill)
        (work (bodyBits s) [] [] [] [] [] [] []))) =
      some (cfg none (ambient .fill)
        (work [] [] [] [] [] [] [] (phaseBits .fill ++ fillNoBody s))) := by
  let tail := encodeWord s.label ++ rawInstanceBits s.items ++ fixedBits s.fixed
  let header := (encodeWord s.item).reverse ++ (encodeWord s.bins).reverse
  have first := unaryCopyTrace .fillNoBins .fillNoItem rfl s.bins (ambient .fill)
    (work [] [] [] [] [] [] [] []) (encodeWord s.item ++ tail) []
  have second := unaryCopyTrace .fillNoItem .incrementLabel rfl s.item (ambient .fill)
    (work [] [] [] [] [] [] [] []) tail (encodeWord s.bins).reverse
  have third := incrementLabelStep (ambient .fill) tail header
  have fourth := copyRestTrace (ambient .fill) tail [] [] [] [] [] (true :: header)
  simp only [io_work, List.append_nil] at first second
  have full := joinTrace (joinTrace (joinTrace first second)
    (oneStepTrace third)) fourth
  simpa [fillNoSteps, bodyBits, fillNoBody, tail, header, encodeWord, List.replicate_succ,
    List.reverse_cons, List.reverse_append, List.reverse_reverse, List.append_assoc,
    Nat.add_assoc] using full

noncomputable def rawTime : Polynomial Nat := Polynomial.C 100 * (Polynomial.X + 1) ^ 2

@[simp] theorem bodyBits_length (s : State) :
    (bodyBits s).length = 3 + s.bins + s.item + s.label +
      (rawInstanceBits s.items).length + (fixedBits s.fixed).length := by
  simp only [bodyBits, List.length_append, encodeWord_length]
  omega

theorem copyBudget_le (s : State) (extra : Nat) (small : extra ≤ 1) :
    1 + (2 * (bodyBits s).length + extra + 3) ≤
      rawTime.eval ((stateBits s).length + 1) := by
  have lengths := stateBits_length s
  simp only [bodyBits_length, rawTime, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

theorem findBudget_le (s : State) :
    1 + findSteps s ≤ rawTime.eval ((stateBits s).length + 1) := by
  have lengths := stateBits_length s
  simp only [findSteps, List.length_append, List.length_cons, List.length_reverse,
    encodeWord_length, rawTime, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

theorem fillNoBudget_le (s : State) :
    1 + fillNoSteps s ≤ rawTime.eval ((stateBits s).length + 1) := by
  have lengths := stateBits_length s
  simp only [fillNoSteps, List.length_append, List.length_cons, List.length_reverse,
    encodeWord_length, rawTime, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

theorem fillBudget_le (s : State) :
    1 + fillSteps s ≤ rawTime.eval ((stateBits s).length + 1) := by
  have lengths := stateBits_length s
  have convert := UnaryToBinaryMachine.steps_le s.label 0
  have fixed := fixedBits_set_length_le s.fixed s.item s.label
  have width : s.label.size ≤ s.label := Nat.size_le.mpr s.label.lt_two_pow_self
  have labelBound : s.label ≤ (stateBits s).length := label_le_stateBits_length s
  have square := Nat.mul_le_mul labelBound labelBound
  simp only [Nat.zero_add] at convert
  simp only [fillSteps, fillPrefixSteps, fillBody, fillHeader, newFixed,
    List.length_append, List.length_cons, List.length_nil, encodeWord_length,
    natBits_length, rawTime, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  rw [Nat.size_eq_bits_len]
  nlinarith

theorem init_eq (input : List Bool) :
    initList machine input = cfg (some .start) (ambient .find)
      (work input [] [] [] [] [] [] []) := by
  unfold initList cfg
  congr 1
  funext k; cases k <;> rfl

private def copyRun (s : State) (answer : Bool) (phase : Ambient) (acc : List Bool)
    (small : acc.length ≤ 1)
    (start : machine.step (cfg (some .start) (ambient .find)
        (work (answer :: stateBits s) [] [] [] [] [] [] [])) =
      some (cfg (some .copyRest) phase (work (bodyBits s) [] [] [] [] [] acc [])))
    (correct : phaseWord phase ++ acc.reverse ++ bodyBits s = stateBits (update s answer)) :
    MachineCanonicalOutput.TerminalRun program (answer :: stateBits s)
      (stateBits (update s answer)) (rawTime.eval (answer :: stateBits s).length) where
  state := (phase, none)
  tapes := work [] [] [] [] [] [] [] (phaseWord phase ++ acc.reverse ++ bodyBits s)
  execution := {
    steps := 1 + (2 * (bodyBits s).length + acc.length + 3)
    evals_in_steps := by
      rw [init_eq]
      change (advance machine.step)^[1 + (2 * (bodyBits s).length + acc.length + 3)] _ = _
      exact joinTrace (oneStepTrace start)
        (copyRestTrace phase (bodyBits s) [] [] [] [] [] acc)
    steps_le_m := by simpa using copyBudget_le s acc.length small }
  output_eq := correct

def rawRun (p : State × Bool) :
    MachineCanonicalOutput.TerminalRun program
      (MachineKeepDecision.typedOutputBits stateBits p)
      (stateBits (SearchMachineComposition.applyAnswer p))
      (rawTime.eval (MachineKeepDecision.typedOutputBits stateBits p).length) := by
  rcases p with ⟨s, answer⟩
  change MachineCanonicalOutput.TerminalRun program (answer :: stateBits s)
    (stateBits (update s answer)) (rawTime.eval (answer :: stateBits s).length)
  have start := startStep s.phase answer (bodyBits s)
  rw [← stateBits_eq] at start
  cases phase : s.phase with
  | done =>
      refine copyRun s answer (ambient .done answer) [] (by simp) ?_ ?_
      · simpa [initialTarget, phase] using start
      · simp [update, phase, stateBits_eq]
  | invalid =>
      refine copyRun s answer (ambient .invalid answer) [] (by simp) ?_ ?_
      · simpa [initialTarget, phase] using start
      · simp [update, phase, stateBits_eq]
  | find =>
      cases answer with
      | false =>
          refine copyRun s false (ambient .find) [true] (by simp) ?_ ?_
          · simpa [initialTarget, phase] using start
          · simp [update, phase, stateBits, phaseBits, bodyBits, encodeWord,
              List.replicate_succ, List.append_assoc]
      | true =>
          refine {
            state := (ambient .fill, none)
            tapes := work [] [] [] [] [] [] [] (phaseBits .fill ++ findBody s)
            execution := {
              steps := 1 + findSteps s
              evals_in_steps := ?_
              steps_le_m := by simpa using findBudget_le s }
            output_eq := ?_ }
          · rw [init_eq]
            change (advance machine.step)^[1 + findSteps s] _ = _
            have first := by simpa only [initialTarget, phase] using start
            exact joinTrace (oneStepTrace first) (findTrace s)
          · simp [program, work, update, phase, stateBits, findBody, encodeWord,
              List.append_assoc]
  | fill =>
      cases answer with
      | false =>
          refine {
            state := (ambient .fill, none)
            tapes := work [] [] [] [] [] [] [] (phaseBits .fill ++ fillNoBody s)
            execution := {
              steps := 1 + fillNoSteps s
              evals_in_steps := ?_
              steps_le_m := by simpa using fillNoBudget_le s }
            output_eq := ?_ }
          · rw [init_eq]
            change (advance machine.step)^[1 + fillNoSteps s] _ = _
            have first := by simpa only [initialTarget, phase] using start
            exact joinTrace (oneStepTrace first) (fillNoTrace s)
          · simp [program, work, update, phase, stateBits, fillNoBody, List.append_assoc]
      | true =>
          refine {
            state := (ambient (fillPhase s), none)
            tapes := work [] [] (fillCounter s).1 [] [] [] []
              (phaseBits (fillPhase s) ++ fillBody s)
            execution := {
              steps := 1 + fillSteps s
              evals_in_steps := ?_
              steps_le_m := by simpa using fillBudget_le s }
            output_eq := ?_ }
          · rw [init_eq]
            change (advance machine.step)^[1 + fillSteps s] _ = _
            have first := by simpa only [initialTarget, phase] using start
            exact joinTrace (oneStepTrace first) (fillTrace s)
          · simp [program, work, update, phase, stateBits, fillBody, fillHeader,
              fillPhase, newFixed, encodeWord, List.append_assoc]

def cleanupTapes : List Tape :=
  [.input, .index, .compare, .binary, .scratch, .payload, .reversed]

theorem cleanup_complete (k : Tape) : k ∈ cleanupTapes ↔ k ≠ program.output := by
  cases k <;> simp [cleanupTapes, program]

noncomputable def computation :
    TM2ComputableInPolyTime (MachineKeepDecision.typedOutputBits stateBits) stateBits
      SearchMachineComposition.applyAnswer :=
  MachineCanonicalOutput.computableInPolyTime program cleanupTapes cleanup_complete
    (MachineKeepDecision.typedOutputBits stateBits) stateBits
    SearchMachineComposition.applyAnswer rawTime rawRun

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet program cleanupTapes cleanup_complete
    (MachineKeepDecision.typedOutputBits stateBits) stateBits
    SearchMachineComposition.applyAnswer rawTime rawRun

end BinPackingGap.SearchUpdateMachine

end OAI
