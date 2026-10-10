import OAI.Computability.BinPacking.Arithmetic.BinaryTallyMachine
import OAI.Computability.BinPacking.Search.SearchInitializeEncoding

namespace OAI

namespace BinPackingGap.SearchFinalizeMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open SearchSemantics SearchEncoding BinaryEncoding
open BinPackingGames.Reduction.MachineTransfer

inductive Tape
  | input | binary | scratch | reversed | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .binary, .scratch, .reversed, .output]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | start
  | convert (label : UnaryToBinaryMachine.Label)
  | emitBinary | skipItem | skipLabel | items
  | numerator | numeratorDigit | denominator | denominatorDigit
  | fixed | option | name | nameDigit | reverse
  deriving DecidableEq, Fintype

abbrev Register := Unit × Option Bool

def tapes (input binary scratch reversed output : List Bool) : Tape → List Bool
  | .input => input
  | .binary => binary
  | .scratch => scratch
  | .reversed => reversed
  | .output => output

@[simp] theorem tapes_input (a b c d e : List Bool) : tapes a b c d e .input = a := rfl
@[simp] theorem tapes_binary (a b c d e : List Bool) : tapes a b c d e .binary = b := rfl
@[simp] theorem tapes_scratch (a b c d e : List Bool) : tapes a b c d e .scratch = c := rfl
@[simp] theorem tapes_reversed (a b c d e : List Bool) : tapes a b c d e .reversed = d := rfl
@[simp] theorem tapes_output (a b c d e : List Bool) : tapes a b c d e .output = e := rfl

@[simp] theorem update_input (a b c d e x : List Bool) :
    Function.update (tapes a b c d e) .input x = tapes x b c d e := by
  funext k; cases k <;> rfl

@[simp] theorem update_binary (a b c d e x : List Bool) :
    Function.update (tapes a b c d e) .binary x = tapes a x c d e := by
  funext k; cases k <;> rfl

@[simp] theorem update_scratch (a b c d e x : List Bool) :
    Function.update (tapes a b c d e) .scratch x = tapes a b x d e := by
  funext k; cases k <;> rfl

@[simp] theorem update_reversed (a b c d e x : List Bool) :
    Function.update (tapes a b c d e) .reversed x = tapes a b c x e := by
  funext k; cases k <;> rfl

@[simp] theorem update_output (a b c d e x : List Bool) :
    Function.update (tapes a b c d e) .output x = tapes a b c d x := by
  funext k; cases k <;> rfl

def go (next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .load (fun _ => ((), none)) (.goto fun _ => next)

def reject : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .push .output (fun _ => false) (.load (fun _ => ((), none)) .halt)

def skipUnary (again next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .pop .input (fun _ head => ((), head))
    (.branch (fun state => state.2.getD false) (go again) (go next))

def skipDigit (next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .pop .input (fun _ head => ((), head)) (go next)

def code : Label → TM2.Stmt (fun _ : Tape => Bool) Label Register
  | .start => .pop .input (fun _ head => ((), head))
      (.branch (fun state => state.2.getD false)
        (.pop .input (fun _ head => ((), head))
          (.branch (fun state => state.2.getD true) reject
            (.push .reversed (fun _ => true) (go (.convert .scan)))))
        reject)
  | .convert label => UnaryToBinaryMachine.instruction .input .binary .scratch
      Label.convert (some .emitBinary) label
  | .emitBinary => .pop .binary (fun _ head => ((), head))
      (.branch (fun state => state.2.isSome)
        (.push .reversed (fun _ => true)
          (.push .reversed (fun state => state.2.getD false) (go .emitBinary)))
        (.push .reversed (fun _ => false) (go .skipItem)))
  | .skipItem => skipUnary .skipItem .skipLabel
  | .skipLabel => skipUnary .skipLabel .items
  | .items => skipUnary .numerator .fixed
  | .numerator => skipUnary .numeratorDigit .denominator
  | .numeratorDigit => skipDigit .numerator
  | .denominator => skipUnary .denominatorDigit .items
  | .denominatorDigit => skipDigit .denominator
  | .fixed => .pop .input (fun _ head => ((), head))
      (.push .reversed (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false) (go .option) (go .reverse)))
  | .option => .pop .input (fun _ head => ((), head))
      (.branch (fun state => state.2.getD false) (go .name)
        (.push .reversed (fun _ => false) (go .fixed)))
  | .name => .pop .input (fun _ head => ((), head))
      (.push .reversed (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false) (go .nameDigit) (go .fixed)))
  | .nameDigit => .pop .input (fun _ head => ((), head))
      (.push .reversed (fun state => state.2.getD false) (go .name))
  | .reverse => loopAt .reversed .output id false .reverse none

def program : MachineCanonicalOutput.Program Tape Label Register where
  input := .input
  output := .output
  main := .start
  initial := ((), none)
  code := code

abbrev machine := MachineCanonicalOutput.sourceMachine program

def cfg (label : Option Label) (input binary scratch reversed output : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, ((), register), tapes input binary scratch reversed output⟩

private theorem oneStepTrace {a b : machine.Cfg} (h : machine.step a = some b) :
    (advance machine.step)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

private theorem transferNext (dst : Tape) : nextAt dst code = advance machine.step := by
  funext state
  rfl

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem skipStep (again next current : Label) (h : code current = skipUnary again next)
    (bit : Bool) (a b c d e : List Bool) :
    machine.step (cfg (some current) (bit :: a) b c d e) =
      some (cfg (some (if bit then again else next)) a b c d e) := by
  change some (TM2.stepAux (code current) _ _) = _
  rw [h]
  cases bit <;> simp [skipUnary, go, TM2.stepAux, cfg]
  all_goals rfl

theorem digitStep (next current : Label) (h : code current = skipDigit next)
    (bit : Bool) (a b c d e : List Bool) :
    machine.step (cfg (some current) (bit :: a) b c d e) =
      some (cfg (some next) a b c d e) := by
  change some (TM2.stepAux (code current) _ _) = _
  rw [h]
  simp [skipDigit, go, TM2.stepAux, cfg]
  all_goals rfl

theorem skipUnaryTrace (current next : Label) (h : code current = skipUnary current next)
    (n : Nat) (a b c d e : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some current) (encodeWord n ++ a) b c d e)) =
      some (cfg (some next) a b c d e) := by
  induction n with
  | zero =>
      simpa only [encodeWord, List.replicate_zero, List.nil_append, List.singleton_append,
        Nat.zero_add, Function.iterate_one, advance_some, Bool.false_eq_true, ↓reduceIte]
        using skipStep current next current h false a b c d e
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp only [encodeWord, List.replicate_succ, List.cons_append, advance_some]
      rw [skipStep current next current h true]
      simpa only [encodeWord, Bool.true_eq, ↓reduceIte] using ih

theorem skipNameTrace (current digit next : Label)
    (hc : code current = skipUnary digit next) (hd : code digit = skipDigit current)
    (bits a b c d e : List Bool) :
    (advance machine.step)^[(BinPackingCompleteness.BinaryEncoding.frame bits).length]
      (some (cfg (some current) (BinPackingCompleteness.BinaryEncoding.frame bits ++ a) b c d e)) =
      some (cfg (some next) a b c d e) := by
  induction bits with
  | nil =>
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.length_singleton,
        List.singleton_append, Function.iterate_one, advance_some,
        Bool.false_eq_true, ↓reduceIte] using skipStep digit next current hc false a b c d e
  | cons bit bits ih =>
      have first := skipStep digit next current hc true
        (bit :: (BinPackingCompleteness.BinaryEncoding.frame bits ++ a)) b c d e
      have second := digitStep current digit hd bit
        (BinPackingCompleteness.BinaryEncoding.frame bits ++ a) b c d e
      simp only [↓reduceIte] at first
      have full := joinTrace (joinTrace
        (oneStepTrace first)
        (oneStepTrace second)) ih
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.length_cons,
        List.cons_append, Nat.add_comm, Nat.add_assoc] using full

theorem skipItemsTrace (r : RawInstance) (a b c d e : List Bool) :
    (advance machine.step)^[(rawInstanceBits r).length]
      (some (cfg (some .items) (rawInstanceBits r ++ a) b c d e)) =
      some (cfg (some .fixed) a b c d e) := by
  induction r with
  | nil =>
      simpa only [rawInstanceBits, listBits, List.length_singleton, List.singleton_append,
        Function.iterate_one, advance_some, Bool.false_eq_true, ↓reduceIte]
        using skipStep .numerator .fixed .items rfl false a b c d e
  | cons q r ih =>
      have first := skipStep .numerator .fixed .items rfl true
        (natBits q.1 ++ natBits q.2 ++ rawInstanceBits r ++ a) b c d e
      have second := skipNameTrace .numerator .numeratorDigit .denominator rfl rfl q.1.bits
        (natBits q.2 ++ rawInstanceBits r ++ a) b c d e
      have third := skipNameTrace .denominator .denominatorDigit .items rfl rfl q.2.bits
        (rawInstanceBits r ++ a) b c d e
      simp only [↓reduceIte] at first
      simp only [natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
        List.append_assoc] at first second third
      have full := joinTrace (joinTrace (joinTrace
        (oneStepTrace first) second) third) ih
      have clock : 1 + (BinPackingCompleteness.BinaryEncoding.frame q.1.bits).length +
          (BinPackingCompleteness.BinaryEncoding.frame q.2.bits).length +
          (rawInstanceBits r).length = (rawInstanceBits (q :: r)).length := by
        simp only [rawInstanceBits, listBits, pairBits, natBits,
          BinPackingCompleteness.BinaryEncoding.nameBits, List.length_cons, List.length_append]
        omega
      rw [clock] at full
      simpa only [rawInstanceBits, listBits, pairBits, natBits,
        BinPackingCompleteness.BinaryEncoding.nameBits, List.length_cons,
        List.length_append, List.cons_append, List.append_assoc, Nat.add_assoc] using full

theorem emitBinaryStep_nil (a c d e : List Bool) :
    machine.step (cfg (some .emitBinary) a [] c d e) =
      some (cfg (some .skipItem) a [] c (false :: d) e) := by
  change some (TM2.stepAux (code .emitBinary) _ _) = _
  simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem emitBinaryStep_cons (bit : Bool) (a b c d e : List Bool) :
    machine.step (cfg (some .emitBinary) a (bit :: b) c d e) =
      some (cfg (some .emitBinary) a b c (bit :: true :: d) e) := by
  change some (TM2.stepAux (code .emitBinary) _ _) = _
  simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem emitBinaryTrace (a bits c d e : List Bool) :
    (advance machine.step)^[bits.length + 1]
      (some (cfg (some .emitBinary) a bits c d e)) =
      some (cfg (some .skipItem) a [] c
        ((BinPackingCompleteness.BinaryEncoding.frame bits).reverse ++ d) e) := by
  induction bits generalizing d with
  | nil => simpa [advance, BinPackingCompleteness.BinaryEncoding.frame] using!
      emitBinaryStep_nil a c d e
  | cons bit bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some, emitBinaryStep_cons]
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.reverse_cons,
        List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using ih (bit :: true :: d)

theorem fixedStep (bit : Bool) (a b c d e : List Bool) :
    machine.step (cfg (some .fixed) (bit :: a) b c d e) =
      some (cfg (some (if bit then .option else .reverse)) a b c (bit :: d) e) := by
  change some (TM2.stepAux (code .fixed) _ _) = _
  cases bit <;> simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem optionStep (bit : Bool) (a b c d e : List Bool) :
    machine.step (cfg (some .option) (bit :: a) b c d e) =
      some (cfg (some (if bit then .name else .fixed)) a b c
        (if bit then d else false :: d) e) := by
  change some (TM2.stepAux (code .option) _ _) = _
  cases bit <;> simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem nameStep (bit : Bool) (a b c d e : List Bool) :
    machine.step (cfg (some .name) (bit :: a) b c d e) =
      some (cfg (some (if bit then .nameDigit else .fixed)) a b c (bit :: d) e) := by
  change some (TM2.stepAux (code .name) _ _) = _
  cases bit <;> simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem nameDigitStep (bit : Bool) (a b c d e : List Bool) :
    machine.step (cfg (some .nameDigit) (bit :: a) b c d e) =
      some (cfg (some .name) a b c (bit :: d) e) := by
  change some (TM2.stepAux (code .nameDigit) _ _) = _
  simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem nameTrace (bits a b c d e : List Bool) :
    (advance machine.step)^[(BinPackingCompleteness.BinaryEncoding.frame bits).length]
      (some (cfg (some .name) (BinPackingCompleteness.BinaryEncoding.frame bits ++ a) b c d e)) =
      some (cfg (some .fixed) a b c
        ((BinPackingCompleteness.BinaryEncoding.frame bits).reverse ++ d) e) := by
  induction bits generalizing d with
  | nil =>
      simpa [BinPackingCompleteness.BinaryEncoding.frame, advance] using! nameStep false a b c d e
  | cons bit bits ih =>
      have first := nameStep true (bit :: (BinPackingCompleteness.BinaryEncoding.frame bits ++ a))
        b c d e
      have second := nameDigitStep bit (BinPackingCompleteness.BinaryEncoding.frame bits ++ a)
        b c (true :: d) e
      simp only [↓reduceIte] at first
      have full := joinTrace (joinTrace
        (oneStepTrace first)
        (oneStepTrace second)) (ih (bit :: true :: d))
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.length_cons,
        List.cons_append, List.reverse_cons, List.append_assoc, List.singleton_append,
        List.nil_append, Nat.add_comm, Nat.add_assoc] using full

theorem fixedTrace (fixed : List (Option Nat)) (a b c d e : List Bool) :
    (advance machine.step)^[(fixedBits fixed).length]
      (some (cfg (some .fixed) (fixedBits fixed ++ a) b c d e)) =
      some (cfg (some .reverse) a b c ((assignmentBits (labels fixed)).reverse ++ d) e) := by
  induction fixed generalizing d with
  | nil =>
      simpa [fixedBits, listBits, labels, assignmentBits, advance] using!
        fixedStep false a b c d e
  | cons value fixed ih =>
      cases value with
      | none =>
          have first := fixedStep true (false :: (fixedBits fixed ++ a)) b c d e
          have second := optionStep false (fixedBits fixed ++ a) b c (true :: d) e
          simp only [Bool.false_eq_true, ↓reduceIte] at first second
          have full := joinTrace (joinTrace
            (oneStepTrace first)
            (oneStepTrace second)) (ih (false :: true :: d))
          have clock : 1 + 1 + (fixedBits fixed).length =
              (fixedBits (none :: fixed)).length := by
            simp only [fixedBits, listBits, optionBits, List.length_cons,
              List.length_append, List.length_nil]
            omega
          rw [clock] at full
          simpa only [fixedBits, listBits, optionBits, labels, List.map_cons,
            Option.getD_none, assignmentBits, natBits,
            BinPackingCompleteness.BinaryEncoding.nameBits, Nat.zero_bits,
            BinPackingCompleteness.BinaryEncoding.frame, List.reverse_cons,
            List.reverse_append, List.reverse_nil, List.cons_append,
            List.nil_append, List.append_nil, List.append_assoc] using full
      | some n =>
          have first := fixedStep true (true :: (natBits n ++ fixedBits fixed ++ a)) b c d e
          have second := optionStep true (natBits n ++ fixedBits fixed ++ a) b c (true :: d) e
          have third := nameTrace n.bits (fixedBits fixed ++ a) b c (true :: d) e
          simp only [↓reduceIte] at first second
          simp only [natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
            List.append_assoc] at first second third
          have full := joinTrace (joinTrace (joinTrace
            (oneStepTrace first)
            (oneStepTrace second)) third)
              (ih ((natBits n).reverse ++ true :: d))
          have clock : 1 + 1 + (BinPackingCompleteness.BinaryEncoding.frame n.bits).length +
              (fixedBits fixed).length = (fixedBits (some n :: fixed)).length := by
            simp only [fixedBits, listBits, optionBits, natBits,
              BinPackingCompleteness.BinaryEncoding.nameBits, List.length_cons, List.length_append]
            omega
          rw [clock] at full
          simpa only [fixedBits, listBits, optionBits, labels, List.map_cons,
            Option.getD_some, assignmentBits, natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
            List.length_cons, List.length_append, List.cons_append, List.reverse_cons,
            List.reverse_append, List.append_assoc, List.singleton_append,
            List.nil_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem convertTrace (n : Nat) (a d e : List Bool) :
    (advance machine.step)^[UnaryToBinaryMachine.steps n 0]
      (some (cfg (some (.convert .scan)) (encodeWord n ++ a) [] [] d e)) =
      some (cfg (some .emitBinary) a n.bits [] d e) := by
  have h := UnaryToBinaryMachine.convertTrace
    (K := Tape) (A := Unit) .input .binary .scratch (by decide) (by decide) (by decide)
    Label.convert (some .emitBinary) code (fun _ => rfl)
    (tapes [] [] [] d e) () n 0 a
  have step_eq : TM2.step code = machine.step := rfl
  rw [step_eq] at h
  simpa [UnaryToBinaryMachine.tapes, cfg] using! h

theorem reverseTrace (a b c d e : List Bool) :
    (advance machine.step)^[d.length + 1]
      (some (cfg (some .reverse) a b c d e)) =
      some (cfg none a b c [] (d.reverse ++ e)) := by
  have h := transferAt_fromTapes (Γ := fun _ : Tape => Bool) .reversed .output
    (by decide) id false .reverse none code rfl (tapes a b c d e) () none
  simpa only [transferNext, cfg, tapes_reversed, tapes_output, tapesAt,
    update_reversed, update_output, List.map_id_fun, id_eq] using! h

theorem startDone (a : List Bool) :
    machine.step (cfg (some .start) (true :: false :: a) [] [] [] []) =
      some (cfg (some (.convert .scan)) a [] [] [true] []) := by
  change some (TM2.stepAux (code .start) _ _) = _
  simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem startFalse (a : List Bool) :
    machine.step (cfg (some .start) (false :: a) [] [] [] []) =
      some (cfg none a [] [] [] [false]) := by
  change some (TM2.stepAux (code .start) _ _) = _
  simp [code, reject, TM2.stepAux, cfg]
  all_goals rfl

theorem startInvalid (a : List Bool) :
    machine.step (cfg (some .start) (true :: true :: a) [] [] [] []) =
      some (cfg none a [] [] [] [false]) := by
  change some (TM2.stepAux (code .start) _ _) = _
  simp [code, reject, TM2.stepAux, cfg]
  all_goals rfl

def bodyBits (s : State) : List Bool :=
  encodeWord s.bins ++ encodeWord s.item ++ encodeWord s.label ++
    rawInstanceBits s.items ++ fixedBits s.fixed

def resultBits (bins : Nat) (fixed : List (Option Nat)) : List Bool :=
  packingResultBits (some ⟨bins, labels fixed⟩)

def doneSteps (s : State) : Nat :=
  1 + UnaryToBinaryMachine.steps s.bins 0 + (s.bins.bits.length + 1) +
    (s.item + 1) + (s.label + 1) + (rawInstanceBits s.items).length +
    (fixedBits s.fixed).length + ((resultBits s.bins s.fixed).length + 1)

theorem doneTrace (s : State) :
    (advance machine.step)^[doneSteps s]
      (some (cfg (some .start) (true :: false :: bodyBits s) [] [] [] [])) =
      some (cfg none [] [] [] [] (resultBits s.bins s.fixed)) := by
  let rest := encodeWord s.item ++ (encodeWord s.label ++
    (rawInstanceBits s.items ++ fixedBits s.fixed))
  let reverseHeader := (natBits s.bins).reverse ++ [true]
  have first := startDone (bodyBits s)
  have second := convertTrace s.bins rest [true] []
  have third := emitBinaryTrace rest s.bins.bits [] [true] []
  have fourth := skipUnaryTrace .skipItem .skipLabel rfl s.item
    (encodeWord s.label ++ (rawInstanceBits s.items ++ fixedBits s.fixed))
    [] [] reverseHeader []
  have fifth := skipUnaryTrace .skipLabel .items rfl s.label
    (rawInstanceBits s.items ++ fixedBits s.fixed) [] [] reverseHeader []
  have sixth := skipItemsTrace s.items (fixedBits s.fixed) [] [] reverseHeader []
  have seventh := fixedTrace s.fixed [] [] [] reverseHeader []
  simp only [List.append_nil] at seventh
  have finalWord :
      ((assignmentBits (labels s.fixed)).reverse ++ reverseHeader).reverse =
        resultBits s.bins s.fixed := by
    simp only [reverseHeader, resultBits, packingResultBits, optionBits, rawPackingBits,
      List.reverse_append, List.reverse_reverse, List.reverse_singleton,
      List.cons_append, List.nil_append]
  have finalLength :
      ((assignmentBits (labels s.fixed)).reverse ++ reverseHeader).length =
        (resultBits s.bins s.fixed).length := by
    simpa only [List.length_reverse] using congrArg List.length finalWord
  have eighth := reverseTrace [] [] []
    ((assignmentBits (labels s.fixed)).reverse ++ reverseHeader) []
  rw [finalLength, finalWord] at eighth
  simp only [List.append_nil] at eighth
  have headerEq :
      (BinPackingCompleteness.BinaryEncoding.frame s.bins.bits).reverse ++ [true] = reverseHeader := rfl
  rw [headerEq] at third
  have firstSecond := joinTrace
    (oneStepTrace first)
    (show (advance machine.step)^[UnaryToBinaryMachine.steps s.bins 0]
      (some (cfg (some (.convert .scan)) (bodyBits s) [] [] [true] [])) = _ from by
        simpa only [bodyBits, rest, List.append_assoc] using second)
  have full := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace firstSecond third) fourth) fifth) sixth) seventh) eighth
  simpa only [doneSteps] using full

theorem labelsBits_le (fixed : List (Option Nat)) :
    (assignmentBits (labels fixed)).length ≤ (fixedBits fixed).length := by
  induction fixed with
  | nil => simp [assignmentBits, labels, fixedBits, listBits]
  | cons value fixed ih =>
      cases value <;>
        simp only [assignmentBits, labels, List.map_cons, fixedBits, listBits,
          optionBits, Option.getD_none, Option.getD_some, List.length_cons,
          List.length_append] at ih ⊢
      · simpa using ih
      · omega

theorem resultBits_length_le (bins : Nat) (fixed : List (Option Nat)) :
    (resultBits bins fixed).length ≤ 2 * bins + (fixedBits fixed).length + 2 := by
  have hf := labelsBits_le fixed
  have hn : bins.size ≤ bins := Nat.size_le.mpr bins.lt_two_pow_self
  simp only [resultBits, packingResultBits, optionBits, rawPackingBits,
    List.length_cons, List.length_append, natBits_length]
  omega

noncomputable def rawTime : Polynomial Nat := 10 * (Polynomial.X + 1) ^ 2

theorem doneSteps_le (s : State) : doneSteps s ≤ rawTime.eval (stateBits s).length := by
  have ht := UnaryToBinaryMachine.steps_le s.bins 0
  have hr := resultBits_length_le s.bins s.fixed
  have hn : s.bins.bits.length ≤ s.bins := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr s.bins.lt_two_pow_self
  have hlen := stateBits_length s
  have hbins : s.bins ≤ (stateBits s).length := by omega
  have hsq : s.bins * s.bins ≤ (stateBits s).length * (stateBits s).length :=
    Nat.mul_le_mul hbins hbins
  simp only [doneSteps, rawTime, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  simp only [Nat.zero_add] at ht
  nlinarith

theorem init_eq (input : List Bool) :
    initList machine input = cfg (some .start) input [] [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  cases k <;> rfl

private def rejectedRun (s : State) (rest : List Bool)
    (h : machine.step (cfg (some .start) (stateBits s) [] [] [] []) =
      some (cfg none rest [] [] [] [false]))
    (hout : packingResultBits (SearchSemantics.output s) = [false]) :
    MachineCanonicalOutput.TerminalRun program (stateBits s)
      (packingResultBits (SearchSemantics.output s)) (rawTime.eval (stateBits s).length) where
  state := ((), none)
  tapes := tapes rest [] [] [] [false]
  execution := {
    steps := 1
    evals_in_steps := by
      change machine.step (initList machine (stateBits s)) = _
      rw [init_eq]
      exact h
    steps_le_m := by
      simp only [rawTime, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      have positive : 1 ≤ (stateBits s).length + 1 := by omega
      have square := Nat.mul_le_mul positive positive
      nlinarith only [square] }
  output_eq := hout.symm

def rawRun (s : State) :
    MachineCanonicalOutput.TerminalRun program (stateBits s)
      (packingResultBits (SearchSemantics.output s)) (rawTime.eval (stateBits s).length) := by
  cases hp : s.phase with
  | find =>
      apply rejectedRun s (false :: bodyBits s)
      · simpa only [stateBits, hp, phaseBits, bodyBits, List.cons_append,
          List.nil_append, List.append_assoc] using startFalse (false :: bodyBits s)
      · simp [SearchSemantics.output, hp, packingResultBits, optionBits]
  | fill =>
      apply rejectedRun s (true :: bodyBits s)
      · simpa only [stateBits, hp, phaseBits, bodyBits, List.cons_append,
          List.nil_append, List.append_assoc] using startFalse (true :: bodyBits s)
      · simp [SearchSemantics.output, hp, packingResultBits, optionBits]
  | invalid =>
      apply rejectedRun s (bodyBits s)
      · simpa only [stateBits, hp, phaseBits, bodyBits, List.cons_append,
          List.nil_append, List.append_assoc] using startInvalid (bodyBits s)
      · simp [SearchSemantics.output, hp, packingResultBits, optionBits]
  | done =>
      refine {
        state := ((), none)
        tapes := tapes [] [] [] [] (resultBits s.bins s.fixed)
        execution := {
          steps := doneSteps s
          evals_in_steps := ?_
          steps_le_m := doneSteps_le s }
        output_eq := ?_ }
      · change (advance machine.step)^[doneSteps s]
          (some (initList machine (stateBits s))) =
            some (cfg none [] [] [] [] (resultBits s.bins s.fixed))
        rw [init_eq]
        simpa only [stateBits, hp, phaseBits, bodyBits,
          List.cons_append, List.nil_append, List.append_assoc] using doneTrace s
      · change resultBits s.bins s.fixed = packingResultBits (SearchSemantics.output s)
        simp only [resultBits, SearchSemantics.output, hp]

def cleanupTapes : List Tape := [.input, .binary, .scratch, .reversed]

theorem cleanup_complete (k : Tape) : k ∈ cleanupTapes ↔ k ≠ program.output := by
  cases k <;> simp [cleanupTapes, program]

noncomputable def computation :
    TM2ComputableInPolyTime stateBits packingResultBits SearchSemantics.output :=
  MachineCanonicalOutput.computableInPolyTime program cleanupTapes cleanup_complete
    stateBits packingResultBits SearchSemantics.output rawTime rawRun

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet program cleanupTapes
    cleanup_complete stateBits packingResultBits SearchSemantics.output rawTime rawRun

end BinPackingGap.SearchFinalizeMachine

end OAI
