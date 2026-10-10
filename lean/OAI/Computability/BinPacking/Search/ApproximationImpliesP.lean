import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import OAI.Computability.BinPacking.Arithmetic.BinaryOrderMachine
import OAI.Computability.BinPacking.Machines.DropPackingBoundMachine
import OAI.Computability.BinPacking.Packing.PackingGapDefinitions

namespace OAI

namespace BinPackingGap

def approximationAccepts (c : Nat) : Option RawPacking → Bool
  | none => false
  | some p => decide (5 * p.bins ≤ p.assignments.length + 5 * c)

@[simp] theorem approximationAccepts_none (c : Nat) :
    approximationAccepts c none = false := rfl

@[simp] theorem approximationAccepts_some (c : Nat) (p : RawPacking) :
    approximationAccepts c (some p) = true ↔
      5 * p.bins ≤ p.assignments.length + 5 * c := by
  simp [approximationAccepts]

theorem approximationAccepts_iff_bins_le (c B : Nat) (r : RawInstance)
    (hcount : r.length = 5 * B) (p : RawPacking)
    (hp : RawPacking.Feasible r p) :
    approximationAccepts c (some p) = true ↔ p.bins ≤ B + c := by
  rw [approximationAccepts_some, hp.1, hcount]
  omega

theorem AbsoluteAdditiveAlgorithm.accepts_of_hasPacking {c : Nat}
    (algorithm : AbsoluteAdditiveAlgorithm c) (r : RawInstance)
    (hr : r.Valid) (B : Nat) (hcount : r.length = 5 * B)
    (hyes : HasPacking (r.toInstance hr) B) :
    approximationAccepts c (algorithm.run (BinaryEncoding.rawInstanceBits r)) = true := by
  obtain ⟨p, hrun, hfeasible, hbound⟩ := algorithm.guarantee r hr
  rw [hrun, approximationAccepts_iff_bins_le c B r hcount p hfeasible]
  exact hbound.trans (Nat.add_le_add_right (opt_le_of_hasPacking hyes) c)

theorem AbsoluteAdditiveAlgorithm.rejects_of_not_hasPacking {c : Nat}
    (algorithm : AbsoluteAdditiveAlgorithm c) (r : RawInstance)
    (hr : r.Valid) (B : Nat) (hcount : r.length = 5 * B)
    (hno : ¬ HasPacking (r.toInstance hr) (B + c)) :
    approximationAccepts c (algorithm.run (BinaryEncoding.rawInstanceBits r)) = false := by
  obtain ⟨p, hrun, hfeasible, _⟩ := algorithm.guarantee r hr
  rw [hrun]
  have hnot : ¬ approximationAccepts c (some p) = true := by
    intro accepted
    have hbins := (approximationAccepts_iff_bins_le c B r hcount p hfeasible).mp accepted
    exact hno ((show HasPacking (r.toInstance hr) p.bins from
      ⟨RawPacking.toPacking r hr p hfeasible⟩).mono hbins)
  cases h : approximationAccepts c (some p) <;> simp_all

theorem PackingGapReduction.approximation_decides {c : Nat} {L : BitLanguage}
    (reduction : PackingGapReduction c L) (algorithm : AbsoluteAdditiveAlgorithm c)
    (x : List Bool) :
    L x ↔ approximationAccepts c
      (algorithm.run (BinaryEncoding.rawInstanceBits (reduction.reduce x).2)) = true := by
  constructor
  · intro hx
    exact algorithm.accepts_of_hasPacking _ (reduction.valid x) _
      (reduction.itemCount x) (reduction.completeness x hx)
  · intro hx
    by_contra hn
    have hf := algorithm.rejects_of_not_hasPacking _ (reduction.valid x) _
      (reduction.itemCount x) (reduction.soundness x hn)
    rw [hx] at hf
    cases hf

end BinPackingGap

namespace BinPackingGap.ApproximationDecisionMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinaryEncoding
open BinPackingCompleteness.BinaryEncoding (bitsValue bitsValue_bits frame)

def borrowPred : List Bool → Option (List Bool)
  | [] => none
  | true :: tail => some (false :: tail)
  | false :: tail => (borrowPred tail).map (true :: ·)

def predWord (bits : List Bool) : List Bool := (borrowPred bits).getD []

theorem borrowPred_value (bits : List Bool) :
    match borrowPred bits with
    | none => bitsValue bits = 0
    | some out => bitsValue bits = bitsValue out + 1 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    cases bit with
    | true => simp [borrowPred, bitsValue, Nat.bit]
    | false =>
      cases h : borrowPred bits with
      | none => simp [borrowPred, h, bitsValue, Nat.bit] at ih ⊢; omega
      | some out => simp [borrowPred, h, bitsValue, Nat.bit] at ih ⊢; omega

theorem borrowPred_length (bits out : List Bool) (h : borrowPred bits = some out) :
    out.length = bits.length := by
  induction bits generalizing out with
  | nil => simp [borrowPred] at h
  | cons bit bits ih =>
    cases bit with
    | true => cases h; rfl
    | false =>
      cases ht : borrowPred bits with
      | none => simp [borrowPred, ht] at h
      | some tail =>
        simp only [borrowPred, ht, Option.map_some, Option.some.injEq] at h
        subst out
        simpa using ih tail ht

theorem predWord_value (bits : List Bool) :
    bitsValue (predWord bits) = bitsValue bits - 1 := by
  have h := borrowPred_value bits
  cases hb : borrowPred bits with
  | none => simp [predWord, hb, bitsValue] at h ⊢; omega
  | some out => simp [predWord, hb] at h ⊢; omega

theorem predWord_length_le (bits : List Bool) : (predWord bits).length ≤ bits.length := by
  cases h : borrowPred bits with
  | none => simp [predWord, h]
  | some out => simp only [predWord, h, Option.getD_some]; exact (borrowPred_length _ _ h).le

def nextCount (count : Fin 5) : Fin 5 :=
  if h : count.val = 4 then 0 else ⟨count.val + 1, by omega⟩

def process (count : Fin 5) (bits : List Bool) : List Nat → List Bool
  | [] => bits
  | _ :: tail => process (nextCount count)
      (if count.val = 4 then predWord bits else bits) tail

theorem process_length_le (count : Fin 5) (bits : List Bool) (assignments : List Nat) :
    (process count bits assignments).length ≤ bits.length := by
  induction assignments generalizing count bits with
  | nil => rfl
  | cons a tail ih =>
    simp only [process]
    by_cases h : count.val = 4
    · simpa only [ite_eq_left h] using
        (ih (nextCount count) (predWord bits)).trans (predWord_length_le bits)
    · simpa only [ite_eq_right h] using ih (nextCount count) bits

theorem process_value (count : Fin 5) (bits : List Bool) (assignments : List Nat) :
    bitsValue (process count bits assignments) =
      bitsValue bits - (count.val + assignments.length) / 5 := by
  induction assignments generalizing count bits with
  | nil => simp [process, Nat.div_eq_of_lt count.isLt]
  | cons a tail ih =>
    by_cases h : count.val = 4
    · have hq : (count.val + (a :: tail).length) / 5 = 1 + tail.length / 5 := by
        simp only [List.length_cons, h]; omega
      simp only [process, ite_eq_left h, nextCount, dite_eq_left h, ih, Fin.val_zero,
        Nat.zero_add, predWord_value, Nat.sub_sub, hq]
    · have hn : (nextCount count).val = count.val + 1 := by simp [nextCount, h]
      simp only [process, ite_eq_right h, ih, hn, List.length_cons]
      congr 2
      omega

theorem process_test (c bins : Nat) (assignments : List Nat) :
    bitsValue (process 0 bins.bits assignments) ≤ c ↔
      5 * bins ≤ assignments.length + 5 * c := by
  rw [process_value, bitsValue_bits]
  simp only [Fin.val_zero, Nat.zero_add]
  omega

inductive Tape
  | input | binary | scratch | constant | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .binary, .scratch, .constant, .output]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | start | binRead | binRestore
  | items (count : Fin 5) | name (count : Fin 5)
  | decrement | predRestore | predDrain | compare | answer (bit : Bool)
  deriving DecidableEq, Fintype

abbrev Register := BinaryOrderMachine.State Unit
abbrev Alphabet (_ : Tape) := Bool

def clean : Register := BinaryOrderMachine.clean ()
def read (head : Option Bool) : Register := ((((), .eq), head), none)
def head (state : Register) : Option Bool := state.1.2

def tapes (input binary scratch constant output : List Bool) : Tape → List Bool
  | .input => input
  | .binary => binary
  | .scratch => scratch
  | .constant => constant
  | .output => output

@[simp] theorem tapes_input (a b d e f : List Bool) : tapes a b d e f .input = a := rfl
@[simp] theorem tapes_binary (a b d e f : List Bool) : tapes a b d e f .binary = b := rfl
@[simp] theorem tapes_scratch (a b d e f : List Bool) : tapes a b d e f .scratch = d := rfl
@[simp] theorem tapes_constant (a b d e f : List Bool) : tapes a b d e f .constant = e := rfl
@[simp] theorem tapes_output (a b d e f : List Bool) : tapes a b d e f .output = f := rfl

@[simp] theorem update_input (a b d e f x : List Bool) :
    Function.update (tapes a b d e f) .input x = tapes x b d e f := by
  funext k; cases k <;> rfl
@[simp] theorem update_binary (a b d e f x : List Bool) :
    Function.update (tapes a b d e f) .binary x = tapes a x d e f := by
  funext k; cases k <;> rfl
@[simp] theorem update_scratch (a b d e f x : List Bool) :
    Function.update (tapes a b d e f) .scratch x = tapes a b x e f := by
  funext k; cases k <;> rfl
@[simp] theorem update_constant (a b d e f x : List Bool) :
    Function.update (tapes a b d e f) .constant x = tapes a b d x f := by
  funext k; cases k <;> rfl
@[simp] theorem update_output (a b d e f x : List Bool) :
    Function.update (tapes a b d e f) .output x = tapes a b d e x := by
  funext k; cases k <;> rfl

def go (label : Label) : TM2.Stmt Alphabet Label Register :=
  .load (fun _ => clean) (.goto fun _ => label)

def finish (bit : Bool) : TM2.Stmt Alphabet Label Register :=
  .push .output (fun _ => bit) (.load (fun _ => clean) .halt)

def pushConstant (bits : List Bool) (next : TM2.Stmt Alphabet Label Register) :
    TM2.Stmt Alphabet Label Register :=
  bits.foldr (fun bit rest => .push .constant (fun _ => bit) rest) next

theorem stepAux_pushConstant (bits : List Bool) (next : TM2.Stmt Alphabet Label Register)
    (state : Register) (base : Tape → List Bool) :
    TM2.stepAux (pushConstant bits next) state base =
      TM2.stepAux next state (Function.update base .constant (bits.reverse ++ base .constant)) := by
  induction bits generalizing base with
  | nil => simp [pushConstant]
  | cons bit bits ih =>
    simp only [pushConstant, List.foldr_cons, TM2.stepAux]
    change TM2.stepAux (pushConstant bits next) state
      (Function.update base .constant (bit :: base .constant)) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

def orderExit : Ordering → Option Label
  | .lt => some (.answer true)
  | .eq => some (.answer true)
  | .gt => some (.answer false)

def code (c : Nat) : Label → TM2.Stmt Alphabet Label Register
  | .start => .pop .input (fun _ bit => read bit)
      (.branch (fun state => (head state).getD false)
        (pushConstant c.bits.reverse (go .binRead)) (finish false))
  | .binRead => .pop .input (fun _ bit => read bit)
      (.branch (fun state => (head state).getD false)
        (.pop .input (fun _ bit => read bit)
          (.push .scratch (fun state => (head state).getD false) (go .binRead)))
        (go .binRestore))
  | .binRestore => loopAt .scratch .binary id false .binRestore (some (.items 0))
  | .items count => .pop .input (fun _ bit => read bit)
      (.branch (fun state => (head state).getD false) (go (.name count)) (go .compare))
  | .name count => .pop .input (fun _ bit => read bit)
      (.branch (fun state => (head state).getD false)
        (.pop .input (fun _ bit => read bit) (go (.name count)))
        (go (if count.val = 4 then .decrement else .items (nextCount count))))
  | .decrement => .pop .binary (fun _ bit => read bit)
      (.branch (fun state => (head state).isNone) (go .predDrain)
        (.branch (fun state => (head state).getD false)
          (.push .binary (fun _ => false) (go .predRestore))
          (.push .scratch (fun _ => true) (go .decrement))))
  | .predRestore => loopAt .scratch .binary id false .predRestore (some (.items 0))
  | .predDrain => .pop .scratch (fun _ bit => read bit)
      (.branch (fun state => (head state).isSome) (go .predDrain) (go (.items 0)))
  | .compare => BinaryOrderMachine.loop .binary .constant .compare orderExit
  | .answer bit => finish bit

def program (c : Nat) : MachineCanonicalOutput.Program Tape Label Register where
  input := .input
  output := .output
  main := .start
  initial := clean
  code := code c

abbrev machine (c : Nat) := MachineCanonicalOutput.sourceMachine (program c)

@[simp] theorem machine_code (c : Nat) (label : Label) :
    (machine c).m label = code c label := rfl

theorem machine_step (c : Nat) : (machine c).step = TM2.step (code c) := rfl

def cfg (label : Option Label) (input binary scratch constant output : List Bool) :
    TM2.Cfg Alphabet Label Register := ⟨label, clean, tapes input binary scratch constant output⟩

private theorem oneStep {c : Nat} {a b : (machine c).Cfg}
    (h : (machine c).step a = some b) :
    (advance (machine c).step)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

private theorem joinTrace {X : Type*} {f : X → X} {a b d : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = d) : f^[n + m] a = d := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem startSome (c : Nat) (input : List Bool) :
    (machine c).step (cfg (some .start) (true :: input) [] [] [] []) =
      some (cfg (some .binRead) input [] [] c.bits []) := by
  change some (TM2.stepAux (code c .start) _ _) = _
  simp [code, TM2.stepAux, cfg, go, read, head, stepAux_pushConstant]

theorem startNone (c : Nat) :
    (machine c).step (cfg (some .start) [false] [] [] [] []) =
      some (cfg none [] [] [] [] [false]) := by
  change some (TM2.stepAux (code c .start) _ _) = _
  simp [code, TM2.stepAux, cfg, finish, read, head]

theorem readBinTrace (c : Nat) (bits suffix binary reversed constant output : List Bool) :
    (advance (machine c).step)^[bits.length + 1]
      (some (cfg (some .binRead) (frame bits ++ suffix) binary reversed constant output)) =
      some (cfg (some .binRestore) suffix binary (bits.reverse ++ reversed) constant output) := by
  induction bits generalizing reversed with
  | nil =>
    apply oneStep
    change some (TM2.stepAux (code c .binRead) _ _) = _
    simp [frame, code, TM2.stepAux, cfg, go, read, head]
    rfl
  | cons bit bits ih =>
    have first : (machine c).step
        (cfg (some .binRead) (frame (bit :: bits) ++ suffix) binary reversed constant output) =
        some (cfg (some .binRead) (frame bits ++ suffix) binary
          (bit :: reversed) constant output) := by
      change some (TM2.stepAux (code c .binRead) _ _) = _
      simp [frame, code, TM2.stepAux, cfg, go, read, head]
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      joinTrace (oneStep first) (ih (bit :: reversed))

theorem restoreTrace (c : Nat) (label : Label) (next : Label)
    (hcode : code c label = loopAt .scratch .binary id false label (some next))
    (input binary scratch constant output : List Bool) :
    (advance (machine c).step)^[scratch.length + 1]
      (some (cfg (some label) input binary scratch constant output)) =
      some (cfg (some next) input (scratch.reverse ++ binary) [] constant output) := by
  have h := transferAt_fromTapes (Γ := Alphabet) Tape.scratch Tape.binary (by decide)
    id false label (some next) (code c) hcode (tapes input binary scratch constant output)
    (((), .eq), none) none
  have hstep : nextAt Tape.binary (code c) = advance (machine c).step := rfl
  rw [hstep] at h
  simpa only [cfg, clean, BinaryOrderMachine.clean, tapes_scratch, tapes_binary,
    List.map_id, tapesAt, update_binary, update_scratch] using! h

def borrowCost : List Bool → Nat → Nat
  | [], n => n + 2
  | true :: _, n => n + 2
  | false :: bits, n => 1 + borrowCost bits (n + 1)

def borrowOutput (bits : List Bool) (n : Nat) : List Bool :=
  match borrowPred bits with
  | none => []
  | some out => List.replicate n true ++ out

theorem borrowCost_le (bits : List Bool) (n : Nat) :
    borrowCost bits n ≤ 2 * bits.length + n + 2 := by
  induction bits generalizing n with
  | nil => simp [borrowCost]
  | cons bit bits ih =>
    cases bit <;> simp [borrowCost]
    have bound := ih (n + 1)
    omega

theorem drainTrace (c : Nat) (input binary scratch constant output : List Bool) :
    (advance (machine c).step)^[scratch.length + 1]
      (some (cfg (some .predDrain) input binary scratch constant output)) =
      some (cfg (some (.items 0)) input binary [] constant output) := by
  induction scratch with
  | nil =>
    apply oneStep
    change some (TM2.stepAux (code c .predDrain) _ _) = _
    simp [code, TM2.stepAux, cfg, go, read, head]
    rfl
  | cons bit tail ih =>
    have first : (machine c).step
        (cfg (some .predDrain) input binary (bit :: tail) constant output) =
        some (cfg (some .predDrain) input binary tail constant output) := by
      change some (TM2.stepAux (code c .predDrain) _ _) = _
      simp [code, TM2.stepAux, cfg, go, read, head]
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      joinTrace (oneStep first) ih

theorem borrowTrace (c : Nat) (bits : List Bool) (n : Nat)
    (input constant output : List Bool) :
    (advance (machine c).step)^[borrowCost bits n]
      (some (cfg (some .decrement) input bits (List.replicate n true) constant output)) =
      some (cfg (some (.items 0)) input (borrowOutput bits n) [] constant output) := by
  induction bits generalizing n with
  | nil =>
    have first : (machine c).step
        (cfg (some .decrement) input [] (List.replicate n true) constant output) =
        some (cfg (some .predDrain) input [] (List.replicate n true) constant output) := by
      change some (TM2.stepAux (code c .decrement) _ _) = _
      simp [code, TM2.stepAux, cfg, go, read, head]
    simpa [borrowCost, borrowOutput, borrowPred, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using joinTrace
      (oneStep first)
      (drainTrace c input [] (List.replicate n true) constant output)
  | cons bit bits ih =>
    cases bit with
    | false =>
      have first : (machine c).step
          (cfg (some .decrement) input (false :: bits) (List.replicate n true) constant output) =
          some (cfg (some .decrement) input bits (List.replicate (n + 1) true) constant output) := by
        change some (TM2.stepAux (code c .decrement) _ _) = _
        simp [code, TM2.stepAux, cfg, go, read, head, List.replicate_succ]
      have hout : borrowOutput bits (n + 1) = borrowOutput (false :: bits) n := by
        unfold borrowOutput
        rw [show borrowPred (false :: bits) = (borrowPred bits).map (true :: ·) from rfl]
        cases h : borrowPred bits with
        | none => rfl
        | some out => simp [List.replicate_add, List.append_assoc]
      simpa only [borrowCost, hout] using joinTrace
        (oneStep first) (ih (n + 1))
    | true =>
      have first : (machine c).step
          (cfg (some .decrement) input (true :: bits) (List.replicate n true) constant output) =
          some (cfg (some .predRestore) input (false :: bits) (List.replicate n true) constant output) := by
        change some (TM2.stepAux (code c .decrement) _ _) = _
        simp [code, TM2.stepAux, cfg, go, read, head]
      simpa [borrowCost, borrowOutput, borrowPred, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using joinTrace
        (oneStep first)
        (restoreTrace c .predRestore (.items 0) rfl input (false :: bits)
          (List.replicate n true) constant output)

theorem decrementTrace (c : Nat) (bits input constant output : List Bool) :
    (advance (machine c).step)^[borrowCost bits 0]
      (some (cfg (some .decrement) input bits [] constant output)) =
      some (cfg (some (.items 0)) input (predWord bits) [] constant output) := by
  have h := borrowTrace c bits 0 input constant output
  cases hb : borrowPred bits <;> simpa [borrowOutput, predWord, hb] using h

theorem nameTrace (c : Nat) (count : Fin 5)
    (bits suffix binary constant output : List Bool) :
    (advance (machine c).step)^[bits.length + 1]
      (some (cfg (some (.name count)) (frame bits ++ suffix) binary [] constant output)) =
      some (cfg (some (if count.val = 4 then .decrement else .items (nextCount count)))
        suffix binary [] constant output) := by
  induction bits with
  | nil =>
    apply oneStep
    change some (TM2.stepAux (code c (.name count)) _ _) = _
    simp [frame, code, TM2.stepAux, cfg, go, read, head]
    rfl
  | cons bit bits ih =>
    have first : (machine c).step
        (cfg (some (.name count)) (frame (bit :: bits) ++ suffix) binary [] constant output) =
        some (cfg (some (.name count)) (frame bits ++ suffix) binary [] constant output) := by
      change some (TM2.stepAux (code c (.name count)) _ _) = _
      simp [frame, code, TM2.stepAux, cfg, go, read, head]
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      joinTrace (oneStep first) ih

def itemsCost (count : Fin 5) (bits : List Bool) : List Nat → Nat
  | [] => 1
  | a :: tail => 1 + (a.size + 1) +
      (if count.val = 4 then borrowCost bits 0 else 0) +
      itemsCost (nextCount count) (if count.val = 4 then predWord bits else bits) tail

theorem itemsTrace (c : Nat) (count : Fin 5) (bits : List Bool)
    (assignments : List Nat) (suffix constant output : List Bool) :
    (advance (machine c).step)^[itemsCost count bits assignments]
      (some (cfg (some (.items count)) (assignmentBits assignments ++ suffix)
        bits [] constant output)) =
      some (cfg (some .compare) suffix (process count bits assignments) [] constant output) := by
  induction assignments generalizing count bits with
  | nil =>
    apply oneStep
    change some (TM2.stepAux (code c (.items count)) _ _) = _
    simp [assignmentBits, listBits, process, code, TM2.stepAux, cfg, go, read, head]
    rfl
  | cons a tail ih =>
    have first : (machine c).step
        (cfg (some (.items count)) (assignmentBits (a :: tail) ++ suffix) bits [] constant output) =
        some (cfg (some (.name count))
          (natBits a ++ (assignmentBits tail ++ suffix)) bits [] constant output) := by
      change some (TM2.stepAux (code c (.items count)) _ _) = _
      simp [assignmentBits, listBits, code, TM2.stepAux, cfg, go, read, head, List.append_assoc]
    have second := nameTrace c count a.bits (assignmentBits tail ++ suffix) bits constant output
    change (advance (machine c).step)^[a.bits.length + 1]
      (some (cfg (some (.name count)) (natBits a ++ (assignmentBits tail ++ suffix))
        bits [] constant output)) = _ at second
    have firstTwo := joinTrace
      (oneStep first) second
    by_cases h : count.val = 4
    · have hc : nextCount count = 0 := by simp [nextCount, h]
      rw [ite_eq_left h] at firstTwo
      have third := decrementTrace c bits (assignmentBits tail ++ suffix) constant output
      have fourth := ih 0 (predWord bits)
      simpa only [itemsCost, process, ite_eq_left h, hc, Nat.size_eq_bits_len,
        Nat.add_assoc] using joinTrace (joinTrace firstTwo third) fourth
    · rw [ite_eq_right h] at firstTwo
      simpa only [itemsCost, process, ite_eq_right h, Nat.add_zero, Nat.size_eq_bits_len,
        Nat.add_assoc] using joinTrace firstTwo (ih (nextCount count) bits)

theorem itemsCost_le (count : Fin 5) (bits : List Bool) (assignments : List Nat) :
    itemsCost count bits assignments ≤
      (assignmentBits assignments).length + (2 * bits.length + 2) * assignments.length := by
  induction assignments generalizing count bits with
  | nil => simp [itemsCost, assignmentBits, listBits]
  | cons a tail ih =>
    have hb := borrowCost_le bits 0
    have hp := predWord_length_le bits
    have hlen : (assignmentBits (a :: tail)).length =
        1 + (2 * a.size + 1) + (assignmentBits tail).length := by
      simp [assignmentBits, listBits]; omega
    by_cases h : count.val = 4
    · have hi := ih (nextCount count) (predWord bits)
      have hm : (2 * (predWord bits).length + 2) * tail.length ≤
          (2 * bits.length + 2) * tail.length := Nat.mul_le_mul_right _ (by omega)
      simp only [itemsCost, ite_eq_left h, List.length_cons, hlen]
      nlinarith
    · have hi := ih (nextCount count) bits
      simp only [itemsCost, ite_eq_right h, List.length_cons, hlen]
      nlinarith

theorem orderExit_eq (a b : Nat) :
    orderExit (BinaryOrderMachine.orderNat a b .eq) = some (.answer (decide (a ≤ b))) := by
  unfold BinaryOrderMachine.orderNat
  split_ifs with hlt hgt
  · simp [orderExit, Nat.le_of_lt hlt]
  · simp [orderExit, Nat.not_le.mpr hgt]
  · have he : a ≤ b := by omega
    simp [orderExit, he]

theorem compareTrace (c : Nat) (bits : List Bool) :
    (advance (machine c).step)^[max bits.length c.bits.length + 2]
      (some (cfg (some .compare) [] bits [] c.bits [])) =
      some (cfg none [] [] [] [] [decide (bitsValue bits ≤ c)]) := by
  have comparison := BinaryOrderMachine.compareTrace_fromTapes
    Tape.binary Tape.constant (by decide) Label.compare orderExit (code c) rfl
    (tapes [] bits [] c.bits []) ()
  have hcomp : (advance (machine c).step)^[max bits.length c.bits.length + 1]
      (some (cfg (some .compare) [] bits [] c.bits [])) =
      some (cfg (some (.answer (decide (bitsValue bits ≤ c)))) [] [] [] [] []) := by
    rw [machine_step]
    simpa only [cfg, clean, tapes_binary, tapes_constant, bitsValue_bits, orderExit_eq,
      tapesAt, update_binary, update_constant] using! comparison
  have answer : (machine c).step
      (cfg (some (.answer (decide (bitsValue bits ≤ c)))) [] [] [] [] []) =
      some (cfg none [] [] [] [] [decide (bitsValue bits ≤ c)]) := by
    change some (TM2.stepAux (code c (.answer _)) _ _) = _
    simp [code, finish, TM2.stepAux, cfg]
  simpa only [Nat.add_assoc] using!
    joinTrace hcomp (oneStep answer)

def someSteps (c : Nat) (p : RawPacking) : Nat :=
  1 + (p.bins.size + 1) + (p.bins.size + 1) +
    itemsCost 0 p.bins.bits p.assignments +
    (max (process 0 p.bins.bits p.assignments).length c.bits.length + 2)

theorem someTrace (c : Nat) (p : RawPacking) :
    (advance (machine c).step)^[someSteps c p]
      (some (cfg (some .start) (packingResultBits (some p)) [] [] [] [])) =
      some (cfg none [] [] [] [] [approximationAccepts c (some p)]) := by
  have first := startSome c (rawPackingBits p)
  have second := readBinTrace c p.bins.bits (assignmentBits p.assignments) [] [] c.bits []
  have third := restoreTrace c .binRestore (.items 0) rfl
    (assignmentBits p.assignments) [] p.bins.bits.reverse c.bits []
  have fourth := itemsTrace c 0 p.bins.bits p.assignments [] c.bits []
  have fifth := compareTrace c (process 0 p.bins.bits p.assignments)
  have hdecision : decide (bitsValue (process 0 p.bins.bits p.assignments) ≤ c) =
      approximationAccepts c (some p) := by
    simp only [approximationAccepts]
    by_cases h : bitsValue (process 0 p.bins.bits p.assignments) ≤ c
    · have rhs := (process_test c p.bins p.assignments).mp h
      simp [h, rhs]
    · have rhs : ¬5 * p.bins ≤ p.assignments.length + 5 * c :=
        fun hh => h ((process_test c p.bins p.assignments).mpr hh)
      simp [h, rhs]
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at second third fourth
  simpa only [someSteps, packingResultBits, optionBits, rawPackingBits,
    natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
    Nat.size_eq_bits_len, hdecision, Nat.add_assoc] using
    joinTrace (joinTrace (joinTrace (joinTrace
      (oneStep first) second) third) fourth) fifth

noncomputable def rawTime (c : Nat) : Polynomial Nat :=
  Polynomial.C (c.size + 20) * (Polynomial.X + 1) ^ 2

theorem someSteps_le (c : Nat) (p : RawPacking) :
    someSteps c p ≤ (rawTime c).eval (packingResultBits (some p)).length := by
  let n := (packingResultBits (some p)).length
  have hlen : n = 2 * p.bins.size + (assignmentBits p.assignments).length + 2 := by
    simp [n, packingResultBits, optionBits, rawPackingBits]; omega
  have hbl : p.bins.bits.length ≤ n := by rw [Nat.size_eq_bits_len]; omega
  have hsize : p.bins.size ≤ n := by omega
  have hal : p.assignments.length ≤ n :=
    (list_length_le_bits_length natBits p.assignments).trans (by
      change (assignmentBits p.assignments).length ≤ n
      omega)
  have hscan := itemsCost_le 0 p.bins.bits p.assignments
  have hscan' : itemsCost 0 p.bins.bits p.assignments ≤ n + (2 * n + 2) * n := by
    have hm : (2 * p.bins.bits.length + 2) * p.assignments.length ≤
        (2 * n + 2) * n := Nat.mul_le_mul (by omega) hal
    omega
  have hprocess := process_length_le 0 p.bins.bits p.assignments
  have hmax : max (process 0 p.bins.bits p.assignments).length c.bits.length ≤ n + c.size := by
    rw [Nat.size_eq_bits_len]
    exact max_le (by omega) (by omega)
  simp only [someSteps, rawTime, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  change _ ≤ (c.size + 20) * (n + 1) ^ 2
  nlinarith

theorem init_eq (c : Nat) (input : List Bool) :
    initList (machine c) input = cfg (some .start) input [] [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  cases k <;> rfl

noncomputable def rawRun (c : Nat) (p : Option RawPacking) :
    MachineCanonicalOutput.TerminalRun (program c) (packingResultBits p)
      [approximationAccepts c p] ((rawTime c).eval (packingResultBits p).length) := by
  cases p with
  | none =>
    refine {
      state := clean
      tapes := tapes [] [] [] [] [false]
      execution := {
        steps := 1
        evals_in_steps := ?_
        steps_le_m := ?_ }
      output_eq := rfl }
    · change (advance (machine c).step)^[1]
        (some (initList (machine c) (packingResultBits none))) = _
      simp only [Function.iterate_one, advance_some]
      rw [init_eq]
      exact startNone c
    · simp [rawTime, packingResultBits, optionBits]
      omega
  | some p =>
    refine {
      state := clean
      tapes := tapes [] [] [] [] [approximationAccepts c (some p)]
      execution := {
        steps := someSteps c p
        evals_in_steps := ?_
        steps_le_m := someSteps_le c p }
      output_eq := rfl }
    change (advance (machine c).step)^[someSteps c p]
      (some (initList (machine c) (packingResultBits (some p)))) = _
    simpa only [init_eq, cfg] using! someTrace c p

def cleanupTapes : List Tape := [.input, .binary, .scratch, .constant]

theorem cleanup_complete (c : Nat) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (program c).output := by
  cases k <;> simp [cleanupTapes, program]

noncomputable def computation (c : Nat) :
    TM2ComputableInPolyTime packingResultBits (fun bit => [bit]) (approximationAccepts c) :=
  MachineCanonicalOutput.computableInPolyTime (program c) cleanupTapes (cleanup_complete c)
    packingResultBits (fun bit => [bit]) (approximationAccepts c) (rawTime c) (rawRun c)

theorem finiteAlphabet (c : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (computation c).tm :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (program c) cleanupTapes
    (cleanup_complete c) packingResultBits (fun bit => [bit]) (approximationAccepts c)
    (rawTime c) (rawRun c)

end BinPackingGap.ApproximationDecisionMachine

noncomputable section

namespace BinPackingGap

open Turing BinPackingGames.Foundations.Complexity

def AbsoluteAdditiveAlgorithm.rawComputation {c : Nat}
    (algorithm : AbsoluteAdditiveAlgorithm c) :
    TM2ComputableInPolyTime BinaryEncoding.rawInstanceBits BinaryEncoding.packingResultBits
      (fun r => algorithm.run (BinaryEncoding.rawInstanceBits r)) where
  tm := algorithm.computation.tm
  inputAlphabet := algorithm.computation.inputAlphabet
  outputAlphabet := algorithm.computation.outputAlphabet
  time := algorithm.computation.time
  outputsFun r := algorithm.computation.outputsFun (BinaryEncoding.rawInstanceBits r)

def PackingGapReduction.approximationComputation {c : Nat} {L : BitLanguage}
    (reduction : PackingGapReduction c L) (algorithm : AbsoluteAdditiveAlgorithm c) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (fun bit => [bit])
      (fun x => approximationAccepts c
        (algorithm.run (BinaryEncoding.rawInstanceBits (reduction.reduce x).2))) :=
by
  let projected := MachineSequential.composeBits reduction.computation
    DropPackingBoundMachine.computation
  let approximated := MachineSequential.composeBits projected algorithm.rawComputation
  let decided := MachineSequential.composeBits approximated
    (ApproximationDecisionMachine.computation c)
  exact decided

theorem PackingGapReduction.approximationComputation_finiteAlphabet
    {c : Nat} {L : BitLanguage} (reduction : PackingGapReduction c L)
    (algorithm : AbsoluteAdditiveAlgorithm c) :
    MachineFiniteAlphabet.FiniteAlphabet (reduction.approximationComputation algorithm).tm := by
  have rawFinite : MachineFiniteAlphabet.FiniteAlphabet algorithm.rawComputation.tm :=
    algorithm.finiteAlphabet
  have projectedFinite := MachineFiniteAlphabet.composeBits reduction.computation
    DropPackingBoundMachine.computation reduction.finiteAlphabet
    DropPackingBoundMachine.finiteAlphabet
  have approximatedFinite := MachineFiniteAlphabet.composeBits
    (MachineSequential.composeBits reduction.computation DropPackingBoundMachine.computation)
    algorithm.rawComputation projectedFinite rawFinite
  exact MachineFiniteAlphabet.composeBits
    (MachineSequential.composeBits
      (MachineSequential.composeBits reduction.computation DropPackingBoundMachine.computation)
      algorithm.rawComputation)
    (ApproximationDecisionMachine.computation c) approximatedFinite
    (ApproximationDecisionMachine.finiteAlphabet c)

theorem PackingGapReduction.inP_of_absoluteAdditiveAlgorithm
    {c : Nat} {L : BitLanguage} (reduction : PackingGapReduction c L)
    (algorithm : AbsoluteAdditiveAlgorithm c) : InP L :=
  ⟨_, reduction.approximationComputation algorithm,
    reduction.approximationComputation_finiteAlphabet algorithm,
    reduction.approximation_decides algorithm⟩

theorem PackingGapNPHard.pEqualsNP_of_absoluteAdditiveAlgorithm {c : Nat}
    (hard : PackingGapNPHard c) (algorithm : AbsoluteAdditiveAlgorithm c) : PEqualsNP := by
  apply pEqualsNP_iff_np_subset_p.mpr
  intro L hL
  obtain ⟨reduction⟩ := hard L hL
  exact reduction.inP_of_absoluteAdditiveAlgorithm algorithm

end BinPackingGap

end

end OAI
