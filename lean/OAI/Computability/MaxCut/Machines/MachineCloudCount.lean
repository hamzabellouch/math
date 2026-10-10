import Mathlib
import OAI.Computability.MaxCut.PCP.ExpanderFamily

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineCloudCount

open Turing
open MachineComposition

inductive Tape
  | original | work | target | scratch | count | spare
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.original, .work, .target, .scratch, .count,
  .spare]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def memory (original work target scratch count spare : List Bool) : Tape → List Bool
  | .original => original
  | .work => work
  | .target => target
  | .scratch => scratch
  | .count => count
  | .spare => spare

@[simp] theorem memory_original (a b c d e f : List Bool) :
    memory a b c d e f .original = a := rfl
@[simp] theorem memory_work (a b c d e f : List Bool) :
    memory a b c d e f .work = b := rfl
@[simp] theorem memory_target (a b c d e f : List Bool) :
    memory a b c d e f .target = c := rfl
@[simp] theorem memory_scratch (a b c d e f : List Bool) :
    memory a b c d e f .scratch = d := rfl
@[simp] theorem memory_count (a b c d e f : List Bool) :
    memory a b c d e f .count = e := rfl
@[simp] theorem memory_spare (a b c d e f : List Bool) :
    memory a b c d e f .spare = f := rfl

@[simp] theorem update_memory_work (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .work x = memory a x c d e f := by
  funext k
  cases k <;> rfl
@[simp] theorem update_memory_target (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .target x = memory a b x d e f := by
  funext k
  cases k <;> rfl
@[simp] theorem update_memory_scratch (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .scratch x = memory a b c x e f := by
  funext k
  cases k <;> rfl
@[simp] theorem update_memory_count (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .count x = memory a b c d x f := by
  funext k
  cases k <;> rfl

variable {Λ σ : Type}

def finishField (restore : Λ) : TM2.Stmt Alphabet Λ (State σ) :=
  .load (fun state => ((state.1.1, false), none)) (.goto fun _ => restore)

def fieldLoop (again restore : Λ) : TM2.Stmt Alphabet Λ (State σ) :=
  .pop .work (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.peek .target (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop .target (fun state _ => (state.1, none))
            (.push .scratch (fun _ => true) (.goto fun _ => again)))
          (.load (fun state => ((state.1.1, true), none)) (.goto fun _ => again))))
      (.peek .target (fun state head => (state.1, head))
        (.branch (fun state => !state.1.2 && !(state.2.getD false))
          (.push .count (fun _ => true) (finishField restore))
          (finishField restore))))

/-- Specification only: equality of the original natural values, unless an
earlier step has already detected overflow. -/
def hit (flag : Bool) (x v : Nat) : Nat := if flag = false ∧ x = v then 1 else 0

theorem fieldStep_zero (again restore : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (original suffix targetSuffix spare : List Bool) (v : Nat)
    (scratch count : List Bool) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program
      ⟨some again, ((ambient, flag), register),
        memory original (encodeWord 0 ++ suffix) (encodeWord v ++ targetSuffix)
          scratch count spare⟩ =
      some ⟨some restore, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) scratch
          (List.replicate (hit flag 0 v) true ++ count) spare⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atField]
  cases v <;> cases flag <;>
    simp [fieldLoop, finishField, TM2.stepAux, encodeWord, hit, List.replicate_succ]

theorem fieldStep_succ_zero (again restore : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (original suffix targetSuffix spare : List Bool) (x : Nat)
    (scratch count : List Bool) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program
      ⟨some again, ((ambient, flag), register),
        memory original (encodeWord (x + 1) ++ suffix) (encodeWord 0 ++ targetSuffix)
          scratch count spare⟩ =
      some ⟨some again, ((ambient, true), none),
        memory original (encodeWord x ++ suffix) (encodeWord 0 ++ targetSuffix)
          scratch count spare⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atField]
  simp [fieldLoop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem fieldStep_succ_succ (again restore : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (original suffix targetSuffix spare : List Bool) (x v : Nat)
    (scratch count : List Bool) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program
      ⟨some again, ((ambient, flag), register),
        memory original (encodeWord (x + 1) ++ suffix)
          (encodeWord (v + 1) ++ targetSuffix) scratch count spare⟩ =
      some ⟨some again, ((ambient, flag), none),
        memory original (encodeWord x ++ suffix) (encodeWord v ++ targetSuffix)
          (true :: scratch) count spare⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atField]
  simp [fieldLoop, TM2.stepAux, encodeWord, List.replicate_succ]

/-- The actual field-reading trace. The scratch holds exactly the consumed
target bits, and the output increment records equality of the complete field. -/
theorem fieldTrace (again restore : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (original suffix targetSuffix spare : List Bool) (x v : Nat)
    (scratch count : List Bool) (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[x + 1]
      (some ⟨some again, ((ambient, flag), register),
        memory original (encodeWord x ++ suffix) (encodeWord v ++ targetSuffix)
          scratch count spare⟩) =
      some ⟨some restore, ((ambient, false), none),
        memory original suffix (encodeWord (v - x) ++ targetSuffix)
          (List.replicate (min x v) true ++ scratch)
          (List.replicate (hit flag x v) true ++ count) spare⟩ := by
  induction x generalizing v scratch flag register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, advance_some, Nat.sub_zero,
        Nat.zero_min, List.replicate_zero, List.nil_append] using
        fieldStep_zero again restore program atField original suffix targetSuffix spare v
          scratch count ambient flag register
  | succ x ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step program))^[x + 1]
        (TM2.step program ⟨some again, ((ambient, flag), register),
          memory original (encodeWord (x + 1) ++ suffix) (encodeWord v ++ targetSuffix)
            scratch count spare⟩) = _
      cases v with
      | zero =>
          rw [fieldStep_succ_zero again restore program atField]
          simpa [hit] using ih 0 scratch true none
      | succ v =>
          rw [fieldStep_succ_succ again restore program atField]
          simpa [hit, Nat.succ_min_succ, List.replicate_succ', List.append_assoc] using
            ih v (true :: scratch) flag none

theorem replicate_encodeWord (a b : Nat) :
    List.replicate a true ++ encodeWord b = encodeWord (a + b) := by
  simp only [encodeWord, ← List.append_assoc, List.replicate_append_replicate]

/-- The actual restoring transfer returns every consumed target bit. -/
theorem preservingFieldTrace (again restore next : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (atRestore : program restore = Reduction.MachineTransfer.loopAt
      .scratch .target id false restore (some next))
    (original suffix targetSuffix count spare : List Bool) (x v : Nat)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[x + min x v + 2]
      (some ⟨some again, ((ambient, false), register),
        memory original (encodeWord x ++ suffix) (encodeWord v ++ targetSuffix)
          [] count spare⟩) =
      some ⟨some next, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if x = v then 1 else 0) true ++ count) spare⟩ := by
  have hfield := fieldTrace again restore program atField original suffix targetSuffix spare
    x v [] count ambient false register
  simp only [List.append_nil, hit, true_and] at hfield
  let after := memory original suffix (encodeWord (v - x) ++ targetSuffix)
    (List.replicate (min x v) true)
    (List.replicate (if x = v then 1 else 0) true ++ count) spare
  have hrestore := Reduction.MachineTransfer.transferAt_fromTapes
    Tape.scratch Tape.target (by decide) id false restore (some next) program atRestore
      after (ambient, false) none
  have hsum : min x v + (v - x) = v := by omega
  simp only [after, memory_scratch, memory_target, List.length_replicate,
    List.reverse_replicate, List.map_id, Reduction.MachineTransfer.tapesAt,
    update_memory_scratch, update_memory_target] at hrestore
  rw [← List.append_assoc, replicate_encodeWord, hsum] at hrestore
  rw [show x + min x v + 2 = (min x v + 1) + (x + 1) by omega,
    Function.iterate_add_apply, hfield]
  exact hrestore

def preservingFieldInTime (again restore next : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (atRestore : program restore = Reduction.MachineTransfer.loopAt
      .scratch .target id false restore (some next))
    (original suffix targetSuffix count spare : List Bool) (x v : Nat)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, ((ambient, false), register),
        memory original (encodeWord x ++ suffix) (encodeWord v ++ targetSuffix)
          [] count spare⟩
      (some ⟨some next, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if x = v then 1 else 0) true ++ count) spare⟩)
      (2 * x + 2) where
  steps := x + min x v + 2
  evals_in_steps := preservingFieldTrace again restore next program atField atRestore
    original suffix targetSuffix count spare x v ambient register
  steps_le_m := by have h := Nat.min_le_left x v; omega

/-- Consecutive concrete field-discard instructions consume a fixed list of
fields. The hypotheses specify code, not an abstract body execution. -/
theorem discardFieldsTrace (labels : Nat → Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (fields : List Nat) (offset : Nat)
    (atField : ∀ i, i < fields.length → program (labels (offset + i)) =
      MachineLookup.discard .work (labels (offset + i)) (labels (offset + i + 1)))
    (original suffix target scratch count spare : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords fields).length]
      (some ⟨some (labels offset), ((ambient, flag), register),
        memory original (encodeWords fields ++ suffix) target scratch count spare⟩) =
      some ⟨some (labels (offset + fields.length)),
        ((ambient, flag), if fields = [] then register else none),
        memory original suffix target scratch count spare⟩ := by
  induction fields generalizing offset register with
  | nil => simp only [encodeWords, List.length_nil, Function.iterate_zero_apply,
      List.nil_append, Nat.add_zero, ↓reduceIte]
  | cons x fields ih =>
      have hfirst := MachineLookup.discardTrace Tape.work (labels offset) (labels (offset + 1))
        program (by simpa only [Nat.add_zero] using atField 0 (by simp))
        (memory original (encodeWords (x :: fields) ++ suffix) target scratch count spare)
        x (encodeWords fields ++ suffix) (by simp only [memory_work, encodeWords, List.append_assoc])
        (ambient, flag) register
      simp only [update_memory_work] at hfirst
      have hrest := ih (offset + 1) (by
        intro i hi
        have h := atField (i + 1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hi)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h) none
      rw [show (encodeWords (x :: fields)).length =
          (encodeWords fields).length + (x + 1) by
          simp only [encodeWords, List.length_append, encodeWord_length]
          omega,
        Function.iterate_add_apply, hfirst]
      simpa only [List.length_cons, List.cons_ne_nil,
        ite_false, ite_self, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

inductive Label
  | copyFirst | copySecond | headerFirst | headerSecond | row | field | restore
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def skipLabel (i : Nat) : Label :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .row

def rowEntry : TM2.Stmt Alphabet Label (State σ) :=
  .peek .work (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.load (fun state => ((state.1.1, false), none)) (.goto fun _ => .field))
      (.load (fun state => ((state.1.1, false), none)) .halt))

/-- A single fixed program copies the input once, skips two headers, then
compares the first field of each 4098-field row. -/
def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .original .spare id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      .spare .original .work false .copySecond (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .row
  | .row => rowEntry
  | .field => fieldLoop .field .restore
  | .restore => Reduction.MachineTransfer.loopAt
      .scratch .target id false .restore (some (skipLabel 0))
  | .skip i => MachineLookup.discard .work (.skip i) (skipLabel (i.val + 1))

theorem program_skip {i : Nat} (hi : i < 4097) :
    program (σ := σ) (skipLabel i) =
      MachineLookup.discard .work (skipLabel i) (skipLabel (i + 1)) := by
  simp only [skipLabel, dite_eq_left hi, program]

theorem rowStep_nonempty (original work target scratch count spare : List Bool)
    (hwork : work ≠ []) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .row, ((ambient, flag), register), memory original work target scratch count spare⟩ =
      some ⟨some .field, ((ambient, false), none),
        memory original work target scratch count spare⟩ := by
  cases work with
  | nil => exact (hwork rfl).elim
  | cons x xs => rfl

theorem rowStep_empty (original target scratch count spare : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .row, ((ambient, flag), register), memory original [] target scratch count spare⟩ =
      some ⟨none, ((ambient, false), none), memory original [] target scratch count spare⟩ := rfl

abbrev Row := Nat × List Nat

def rowWords (r : Row) : List Nat := r.1 :: r.2

def rowTime (v : Nat) (r : Row) : Nat :=
  (encodeWords (rowWords r)).length + min r.1 v + 2

/-- One complete stored row is consumed; the target and original are restored. -/
theorem rowTrace (r : Row) (hwidth : r.2.length = 4097) (v : Nat)
    (original suffix targetSuffix count spare : List Bool) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[rowTime v r]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
          [] count spare⟩) =
      some ⟨some .row, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if r.1 = v then 1 else 0) true ++ count) spare⟩ := by
  have hfield := preservingFieldTrace Label.field Label.restore (skipLabel 0)
    program rfl rfl original (encodeWords r.2 ++ suffix) targetSuffix count spare r.1 v ambient none
  have hskip := discardFieldsTrace skipLabel (program (σ := σ)) r.2 0
    (by intro i hi; simpa only [Nat.zero_add] using program_skip (hwidth ▸ hi))
    original suffix (encodeWord v ++ targetSuffix) []
    (List.replicate (if r.1 = v then 1 else 0) true ++ count) spare ambient false none
  have hnonempty : r.2 ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, skipLabel, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false] at hskip
  have htime : rowTime v r = (encodeWords r.2).length + (r.1 + min r.1 v + 2) + 1 := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [htime, Function.iterate_succ_apply]
  change (advance (TM2.step (program (σ := σ))))^[
      (encodeWords r.2).length + (r.1 + min r.1 v + 2)]
    (TM2.step program ⟨some .row, ((ambient, false), register),
      memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
        [] count spare⟩) = _
  rw [rowStep_nonempty original _ _ [] count spare
    (by simp [rowWords, encodeWords, encodeWord]) ambient false register,
    Function.iterate_add_apply]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hfield]
  exact hskip

def rowsHits (v : Nat) : List Row → Nat
  | [] => 0
  | r :: rs => (if r.1 = v then 1 else 0) + rowsHits v rs

def rowsTime (v : Nat) : List Row → Nat
  | [] => 1
  | r :: rs => rowsTime v rs + rowTime v r

/-- The complete actual row scan halts with the number of matching tails. -/
theorem rowsTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097) (v : Nat)
    (original targetSuffix count spare : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[rowsTime v rs]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rs.flatMap rowWords)) (encodeWord v ++ targetSuffix)
          [] count spare⟩) =
      some ⟨none, ((ambient, false), none),
        memory original [] (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) spare⟩ := by
  induction rs generalizing count register with
  | nil =>
      simpa only [rowsTime, List.flatMap_nil, encodeWords, Function.iterate_one, advance_some,
        rowsHits, List.replicate_zero, List.nil_append] using
        rowStep_empty original (encodeWord v ++ targetSuffix) [] count spare ambient false register
  | cons r rs ih =>
      have hrow := rowTrace r (hwidth r (by simp)) v original
        (encodeWords (rs.flatMap rowWords)) targetSuffix count spare ambient register
      have hrest := ih (by intro x hx; exact hwidth x (by simp [hx]))
        (List.replicate (if r.1 = v then 1 else 0) true ++ count) none
      simp only [rowsTime, List.flatMap_cons, encodeWords_append]
      rw [Function.iterate_add_apply, hrow]
      simpa only [rowsHits, ← List.append_assoc, List.replicate_append_replicate,
        Nat.add_comm] using hrest

theorem rowTime_le (v : Nat) (r : Row) :
    rowTime v r ≤ 3 * (encodeWords (rowWords r)).length := by
  have hmin := Nat.min_le_left r.1 v
  have hlen : r.1 + 1 ≤ (encodeWords (rowWords r)).length := by
    simp only [rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  unfold rowTime
  omega

theorem rowsTime_le (v : Nat) (rs : List Row) :
    rowsTime v rs ≤ 3 * (encodeWords (rs.flatMap rowWords)).length + 1 := by
  induction rs with
  | nil => simp only [rowsTime, List.flatMap_nil, encodeWords, List.length_nil,
      Nat.mul_zero, Nat.zero_add, le_refl]
  | cons r rs ih =>
      have hr := rowTime_le v r
      simp only [rowsTime, List.flatMap_cons, encodeWords_append, List.length_append]
      omega

def inputWord (n m : Nat) (rs : List Row) : List Bool :=
  encodeWords ([n, m] ++ rs.flatMap rowWords)

theorem inputWord_eq (n m : Nat) (rs : List Row) :
    inputWord n m rs = encodeWord n ++ (encodeWord m ++ encodeWords (rs.flatMap rowWords)) := by
  simp only [inputWord, encodeWords_append, encodeWords, List.append_nil, List.append_assoc]

theorem inputWord_length (n m : Nat) (rs : List Row) :
    (inputWord n m rs).length = n + 1 + (m + 1) +
      (encodeWords (rs.flatMap rowWords)).length := by
  rw [inputWord_eq]
  simp only [List.length_append, encodeWord_length]
  omega

def totalSteps (n m v : Nat) (rs : List Row) : Nat :=
  2 * ((inputWord n m rs).length + 1) + (n + 1) + (m + 1) + rowsTime v rs

/-- One preserving copy, the two concrete header discards, and the proved row
scan form the complete execution. The input and target tapes are unchanged. -/
theorem countTrace (n m v : Nat) (rs : List Row)
    (hwidth : ∀ r ∈ rs, r.2.length = 4097)
    (targetSuffix count : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[totalSteps n m v rs]
      (some ⟨some .copyFirst, ((ambient, false), register),
        memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) [] count []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) []⟩ := by
  have hcopy := MachineCopy.copyTrace Tape.original Tape.work Tape.spare
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.headerFirst) program rfl rfl
    (memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) [] count [])
    rfl (ambient, false) register
  simp only [memory_original, memory_work, List.append_nil, update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace Tape.work Label.headerFirst Label.headerSecond
    program rfl
    (memory (inputWord n m rs) (inputWord n m rs) (encodeWord v ++ targetSuffix) [] count [])
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (by exact inputWord_eq n m rs) (ambient, false) none
  simp only [update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace Tape.work Label.headerSecond Label.row
    program rfl
    (memory (inputWord n m rs) (encodeWord m ++ encodeWords (rs.flatMap rowWords))
      (encodeWord v ++ targetSuffix) [] count [])
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [update_memory_work] at hsecond
  have hrows := rowsTrace rs hwidth v (inputWord n m rs) targetSuffix count [] ambient none
  rw [show totalSteps n m v rs = rowsTime v rs + ((m + 1) + ((n + 1) +
      2 * ((inputWord n m rs).length + 1))) by unfold totalSteps; omega,
    Function.iterate_add_apply _ (rowsTime v rs),
    Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
    hcopy, hfirst, hsecond]
  exact hrows

theorem totalSteps_le (n m v : Nat) (rs : List Row) :
    totalSteps n m v rs ≤ 5 * (inputWord n m rs).length + 3 := by
  have hrows := rowsTime_le v rs
  have hlen := inputWord_length n m rs
  unfold totalSteps
  omega

open MaxCutGames.Foundations.PCP

def tableRows (t : GraphTables.Table) : List Row :=
  (GraphTables.rowList t).map (fun r =>
    (r.tail.val, r.reverseIndex.val :: GraphTables.relationWords r.relation))

theorem tableRows_width (t : GraphTables.Table) :
    ∀ r ∈ tableRows t, r.2.length = 4097 := by
  intro r hr
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
  simp [GraphTables.relationWords]

theorem tableRows_words (t : GraphTables.Table) :
    (tableRows t).flatMap rowWords = (GraphTables.rowList t).flatMap GraphTables.rowWords := by
  simp only [tableRows, List.flatMap_map]
  apply congrArg (fun f => (GraphTables.rowList t).flatMap f)
  funext r
  rfl

theorem tableRows_input (t : GraphTables.Table) :
    inputWord t.vertices t.darts (tableRows t) = GraphTables.tableBits t := by
  rw [inputWord, tableRows_words]
  rfl

theorem rowsHits_eq_filter (v : Nat) (rs : List Row) :
    rowsHits v rs = (rs.filter (fun r => decide (r.1 = v))).length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      by_cases h : r.1 = v <;> simp [rowsHits, h, ih, Nat.add_comm]

theorem rowList_eq_finRange_map (t : GraphTables.Table) :
    GraphTables.rowList t = (List.finRange t.darts).map (fun e => t.rows[e]) := by
  apply List.ext_getElem
  · simp [GraphTables.rowList]
  · intro i hi hj
    simp [GraphTables.rowList]

theorem rowList_cloud_count (t : GraphTables.Table) (v : Fin t.vertices) :
    ((GraphTables.rowList t).filter (fun r => decide (r.tail = v))).length =
      PreprocessingCloudIndex.cloudSize t v := by
  rw [rowList_eq_finRange_map, List.filter_map, List.length_map]
  rfl

theorem tableRows_hits (t : GraphTables.Table) (v : Fin t.vertices) :
    rowsHits v.val (tableRows t) = PreprocessingCloudIndex.cloudSize t v := by
  rw [rowsHits_eq_filter]
  simp only [tableRows, List.filter_map, List.length_map]
  simpa only [Function.comp_def, Fin.val_inj] using rowList_cloud_count t v

/-- Cloud size is produced by reading the actual encoded tail fields, with
the complete graph input and unary vertex query preserved on their tapes. -/
theorem cloudCountTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (targetSuffix countSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[totalSteps t.vertices t.darts v.val (tableRows t)]
      (some ⟨some .copyFirst, ((ambient, false), register),
        memory (GraphTables.tableBits t) [] (encodeWord v.val ++ targetSuffix) []
          (encodeWord 0 ++ countSuffix) []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t) [] (encodeWord v.val ++ targetSuffix) []
          (encodeWord (PreprocessingCloudIndex.cloudSize t v) ++ countSuffix) []⟩ := by
  have h := countTrace t.vertices t.darts v.val (tableRows t) (tableRows_width t)
    targetSuffix (encodeWord 0 ++ countSuffix) ambient register
  rw [tableRows_input, tableRows_hits, ← List.append_assoc, replicate_encodeWord, Nat.add_zero] at h
  exact h

/-- A linear transition budget for this concrete cloud-count subroutine. -/
def cloudCountInTime (t : GraphTables.Table) (v : Fin t.vertices)
    (targetSuffix countSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (σ := σ)))
      ⟨some .copyFirst, ((ambient, false), register),
        memory (GraphTables.tableBits t) [] (encodeWord v.val ++ targetSuffix) []
          (encodeWord 0 ++ countSuffix) []⟩
      (some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t) [] (encodeWord v.val ++ targetSuffix) []
          (encodeWord (PreprocessingCloudIndex.cloudSize t v) ++ countSuffix) []⟩)
      (5 * (GraphTables.tableBits t).length + 3) where
  steps := totalSteps t.vertices t.darts v.val (tableRows t)
  evals_in_steps := cloudCountTrace t v targetSuffix countSuffix ambient register
  steps_le_m := by
    simpa only [tableRows_input] using totalSteps_le t.vertices t.darts v.val (tableRows t)

end MaxCutGames.Foundations.Complexity.MachineCloudCount

namespace MaxCutGames.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open MaxCutGames.Foundations.PCP

inductive Tape
  | input | work | power | saved | level | fuel | spare | product
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .work, .power, .saved, .level, .fuel,
  .spare, .product]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | init | fuelFirst | fuelSecond | guard | copyFirst | copySecond
  | compare | restore | decide | scale | transfer | cleanup
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.init, .fuelFirst, .fuelSecond, .guard,
  .copyFirst, .copySecond, .compare, .restore, .decide, .scale, .transfer, .cleanup]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def memory (input work power saved level fuel spare product : List Bool) : Tape → List Bool
  | .input => input
  | .work => work
  | .power => power
  | .saved => saved
  | .level => level
  | .fuel => fuel
  | .spare => spare
  | .product => product

@[simp] theorem update_work (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .work x = memory a x c d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_power (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .power x = memory a b x d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_saved (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .saved x = memory a b c x e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_level (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .level x = memory a b c d x f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_fuel (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .fuel x = memory a b c d e x g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_product (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .product x = memory a b c d e f g x := by
  funext k; cases k <;> rfl

variable {σ : Type}

def compareLoop : TM2.Stmt Alphabet Label (State σ) :=
  .pop .work (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.peek .power (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop .power (fun state _ => (state.1, none))
            (.push .saved (fun _ => true) (.goto fun _ => .compare)))
          (.load (fun state => ((state.1.1, true), none)) (.goto fun _ => .compare))))
      (.load (fun state => (state.1, none)) (.goto fun _ => .restore)))

/-- Each input tally emits the fixed block of `g` tallies. The delimiter
starts the new power and the level is incremented by an actual push. -/
def scaleLoop (g : Nat) : TM2.Stmt Alphabet Label (State σ) :=
  .pop .power (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (Reduction.MachineSubstitution.pushWord .product (List.replicate g true)
        (.goto fun _ => .scale))
      (.push .power (fun _ => false)
        (.push .level (fun _ => true)
          (.load (fun state => (state.1, none)) (.goto fun _ => .transfer)))))

def program (g : Nat) : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push .power (fun _ => false) (.push .power (fun _ => true)
      (.push .level (fun _ => false) (.goto fun _ => .fuelFirst)))
  | .fuelFirst => Reduction.MachineTransfer.loopAt
      .input .spare id false .fuelFirst (some .fuelSecond)
  | .fuelSecond => MachineCopy.forkLoop
      .spare .input .fuel false .fuelSecond (some .guard)
  | .guard => MachineUnaryCounter.guard .fuel .copyFirst .cleanup
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .input .spare id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      .spare .input .work false .copySecond (some .compare)
  | .compare => compareLoop
  | .restore => Reduction.MachineTransfer.loopAt
      .saved .power id false .restore (some .decide)
  | .decide => .branch (fun state => state.1.2)
      (.load (fun state => ((state.1.1, false), none)) (.goto fun _ => .scale))
      (.load (fun state => ((state.1.1, false), none)) (.goto fun _ => .cleanup))
  | .scale => scaleLoop g
  | .transfer => Reduction.MachineTransfer.loopAt
      .product .power id false .transfer (some .guard)
  | .cleanup => MachineDrain.drain .fuel .cleanup none

def overflow (flag : Bool) (x p : Nat) : Bool := flag || decide (p < x)

theorem compareStep_zero (g p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord 0) (encodeWord p) saved level fuel spare product⟩ =
      some ⟨some .restore, ((ambient, flag), none),
        memory input [] (encodeWord p) saved level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord]

theorem compareStep_succ_zero (g x : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord (x + 1)) (encodeWord 0) saved level fuel spare product⟩ =
      some ⟨some .compare, ((ambient, true), none),
        memory input (encodeWord x) (encodeWord 0) saved level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

theorem compareStep_succ_succ (g x p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord (x + 1)) (encodeWord (p + 1)) saved level fuel spare product⟩ =
      some ⟨some .compare, ((ambient, flag), none),
        memory input (encodeWord x) (encodeWord p) (true :: saved) level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

/-- The comparison is performed by actual finite-head transitions. -/
theorem compareTrace (g x p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step (program g)))^[x + 1]
      (some ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord x) (encodeWord p) saved level fuel spare product⟩) =
      some ⟨some .restore, ((ambient, overflow flag x p), none),
        memory input [] (encodeWord (p - x))
          (List.replicate (min x p) true ++ saved) level fuel spare product⟩ := by
  induction x generalizing p saved flag register with
  | zero =>
      simpa [overflow] using compareStep_zero g p input saved level fuel spare product ambient flag register
  | succ x ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step (program g)))^[x + 1]
        (TM2.step (program g) ⟨some .compare, ((ambient, flag), register),
          memory input (encodeWord (x + 1)) (encodeWord p) saved level fuel spare product⟩) = _
      cases p with
      | zero =>
          rw [compareStep_succ_zero]
          simpa [overflow] using ih 0 saved true none
      | succ p =>
          rw [compareStep_succ_succ]
          simpa [overflow, Nat.succ_min_succ, List.replicate_succ', List.append_assoc] using
            ih p (true :: saved) flag none

theorem replicate_encodeWord (a b : Nat) :
    List.replicate a true ++ encodeWord b = encodeWord (a + b) := by
  simp only [encodeWord, ← List.append_assoc, List.replicate_append_replicate]

theorem compareRestoredTrace (g k p : Nat) (level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[k + min k p + 2]
      (some ⟨some .compare, ((ambient, false), register),
        memory (encodeWord k) (encodeWord k) (encodeWord p) [] level fuel [] []⟩) =
      some ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] level fuel [] []⟩ := by
  have hc := compareTrace g k p (encodeWord k) [] level fuel [] [] ambient false register
  simp only [overflow, Bool.false_or, List.append_nil] at hc
  let mid := memory (encodeWord k) [] (encodeWord (p - k))
    (List.replicate (min k p) true) level fuel [] []
  have hr := Reduction.MachineTransfer.transferAt_fromTapes Tape.saved Tape.power (by decide)
    id false Label.restore (some Label.decide) (program g) rfl mid (ambient, decide (p < k)) none
  have hsum : min k p + (p - k) = p := by omega
  simp only [mid, memory, List.length_replicate, List.reverse_replicate, List.map_id,
    Reduction.MachineTransfer.tapesAt, update_saved, update_power] at hr
  rw [replicate_encodeWord, hsum] at hr
  rw [show k + min k p + 2 = (min k p + 1) + (k + 1) by omega,
    Function.iterate_add_apply, hc]
  exact hr

private theorem appendTrace_inline_MachineCeilingPower {α : Type*} (f : α → α) {a b c : α} {s t : Nat}
    (hs : f^[s] a = b) (ht : f^[t] b = c) : f^[s + t] a = c := by
  rw [Nat.add_comm s t, Function.iterate_add_apply, hs, ht]

theorem scaleStep_succ (g p b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord (p + 1)) [] level fuel [] (List.replicate b true)⟩ =
      some ⟨some .scale, ((ambient, false), some true),
        memory input [] (encodeWord p) [] level fuel [] (List.replicate (g + b) true)⟩ := by
  change some (TM2.stepAux (scaleLoop g) _ _) = _
  simp [scaleLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ,
    Reduction.MachineSubstitution.stepAux_pushWord]

theorem scaleStep_zero (g b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord 0) [] level fuel [] (List.replicate b true)⟩ =
      some ⟨some .transfer, ((ambient, false), none),
        memory input [] (encodeWord 0) [] (true :: level) fuel [] (List.replicate b true)⟩ := by
  change some (TM2.stepAux (scaleLoop g) _ _) = _
  simp [scaleLoop, TM2.stepAux, memory, encodeWord]

theorem scaleScanTrace (g p b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[p + 1]
      (some ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord p) [] level fuel [] (List.replicate b true)⟩) =
      some ⟨some .transfer, ((ambient, false), none),
        memory input [] (encodeWord 0) [] (true :: level) fuel [] (List.replicate (g * p + b) true)⟩ := by
  induction p generalizing b register with
  | zero => simpa using scaleStep_zero g b input level fuel ambient register
  | succ p ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step (program g)))^[p + 1]
        (TM2.step (program g) ⟨some .scale, ((ambient, false), register),
          memory input [] (encodeWord (p + 1)) [] level fuel [] (List.replicate b true)⟩) = _
      rw [scaleStep_succ, ih]
      have h : g * p + (g + b) = g * (p + 1) + b := by rw [Nat.mul_succ]; omega
      rw [h]

/-- The fixed-coefficient unary multiplication is an actual scan and transfer;
the level increment is one explicit push in the final scan transition. -/
theorem scaleTrace (g k p e : Nat) (fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[p + g * p + 2]
      (some ⟨some .scale, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) fuel [] []⟩) =
      some ⟨some .guard, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (p * g)) [] (encodeWord (e + 1)) fuel [] []⟩ := by
  have hs := scaleScanTrace g p 0 (encodeWord k) (encodeWord e) fuel ambient register
  simp only [List.replicate_zero, Nat.add_zero] at hs
  let mid := memory (encodeWord k) [] (encodeWord 0) [] (true :: encodeWord e) fuel []
    (List.replicate (g * p) true)
  have ht := Reduction.MachineTransfer.transferAt_fromTapes Tape.product Tape.power (by decide)
    id false Label.transfer (some Label.guard) (program g) rfl mid (ambient, false) none
  simp only [mid, memory, List.length_replicate, List.reverse_replicate, List.map_id,
    Reduction.MachineTransfer.tapesAt, update_product, update_power,
    replicate_encodeWord, Nat.add_zero] at ht
  have he : true :: encodeWord e = encodeWord (e + 1) := by simp [encodeWord, List.replicate_succ]
  rw [he, Nat.mul_comm g p] at ht
  rw [he, Nat.mul_comm g p] at hs
  have h := appendTrace_inline_MachineCeilingPower (advance (TM2.step (program g))) hs ht
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using h

theorem cleanupTrace (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[f + 2]
      (some ⟨some .cleanup, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] []⟩ := by
  have h := MachineDrain.drainTrace Tape.fuel Label.cleanup none (program g) rfl
    (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    (encodeWord f) (ambient, false) register
  simpa only [encodeWord_length, update_fuel, Nat.add_assoc] using h

theorem guardStep_succ (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩ =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  have h := MachineUnaryCounter.guardStep_succ Tape.fuel Label.guard Label.copyFirst Label.cleanup
    (program g) rfl (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    f [] (ambient, false) register
  simpa only [MachineUnaryCounter.counterTapes, List.append_nil, update_fuel] using h

theorem guardStep_zero (g k p e : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ =
      some ⟨some .cleanup, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ := by
  have h := MachineUnaryCounter.guardStep_zero Tape.fuel Label.guard Label.copyFirst Label.cleanup
    (program g) rfl (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    [] (ambient, false) register
  simpa only [MachineUnaryCounter.counterTapes, List.append_nil, update_fuel] using h

theorem decideStep (g k p e f : Nat) (ambient : σ) :
    TM2.step (program g)
      ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  by_cases h : k ≤ p
  · have hn : ¬p < k := by omega
    simp [TM2.step, program, TM2.stepAux, h, hn]
  · have hn : p < k := by omega
    simp [TM2.step, program, TM2.stepAux, h, hn]

def prefixTime (k p : Nat) : Nat := (1 + 2 * (k + 2)) + (k + min k p + 2) + 1

/-- The loop prefix is an actual guard, preserving copy, comparison,
restoration and finite decision, all in the same fixed program. -/
theorem prefixTrace (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[prefixTime k p]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩) =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  have hg : (advance (TM2.step (program g)))^[1]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ :=
    guardStep_succ g k p e f ambient register
  have hc := MachineCopy.copyTrace Tape.input Tape.work Tape.spare
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.compare) (program g) rfl rfl
    (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] [])
    rfl (ambient, false) none
  simp only [memory, encodeWord_length, List.append_nil, update_work] at hc
  have hcmp := compareRestoredTrace g k p (encodeWord e) (encodeWord f) ambient none
  have hd : (advance (TM2.step (program g)))^[1]
      (some ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ :=
    decideStep g k p e f ambient
  exact appendTrace_inline_MachineCeilingPower _ (appendTrace_inline_MachineCeilingPower _ (appendTrace_inline_MachineCeilingPower _ hg hc) hcmp) hd

def coreTime (g k : Nat) : Nat → Nat → Nat
  | 0, _ => 3
  | f + 1, p => prefixTime k p +
      if k ≤ p then f + 2 else (p + g * p + 2) + coreTime g k f (p * g)

/-- The fixed machine realizes the exact previously checked bounded loop.
Every initial fuel tally is either used or cleared before halting. -/
theorem coreTrace (g k f e p : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[coreTime g k f p]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) []
          (encodeWord (PreprocessingLevels.levelLoop g k f e p).2) []
          (encodeWord (PreprocessingLevels.levelLoop g k f e p).1) [] [] []⟩ := by
  induction f generalizing e p register with
  | zero =>
      have hg : (advance (TM2.step (program g)))^[1]
          (some ⟨some .guard, ((ambient, false), register),
            memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩) =
          some ⟨some .cleanup, ((ambient, false), none),
            memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ :=
        guardStep_zero g k p e ambient register
      exact appendTrace_inline_MachineCeilingPower _ hg (cleanupTrace g k p e 0 ambient none)
  | succ f ih =>
      have hpref := prefixTrace g k p e f ambient register
      by_cases h : k ≤ p
      · simp only [h, ite_true] at hpref
        have hrun := appendTrace_inline_MachineCeilingPower _ hpref (cleanupTrace g k p e f ambient none)
        simpa only [coreTime, PreprocessingLevels.levelLoop, h, ite_true] using hrun
      · simp only [h, ite_false] at hpref
        have hscale := scaleTrace g k p e (encodeWord f) ambient none
        have hrun := appendTrace_inline_MachineCeilingPower _ hpref (appendTrace_inline_MachineCeilingPower _ hscale (ih (e + 1) (p * g) none))
        simpa only [coreTime, PreprocessingLevels.levelLoop, h, ite_false] using hrun

def roundBudget (g k : Nat) : Nat := (g + 8) * (k + 1) + 16

theorem prefixTime_le (k p : Nat) : prefixTime k p ≤ 4 * k + 8 := by
  have h := Nat.min_le_left k p
  unfold prefixTime
  omega

theorem prefixTime_le_roundBudget (g k p : Nat) : prefixTime k p ≤ roundBudget g k := by
  have h := prefixTime_le k p
  unfold roundBudget
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

theorem continuingTime_le (g k p : Nat) (h : p < k) :
    prefixTime k p + (p + g * p + 2) ≤ roundBudget g k := by
  have hprefix := prefixTime_le k p
  have hmul := Nat.mul_le_mul_left g h.le
  unfold roundBudget
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

theorem coreTime_le (g k f p : Nat) :
    coreTime g k f p ≤ (f + 1) * roundBudget g k := by
  have hB : 3 ≤ roundBudget g k := by unfold roundBudget; omega
  induction f generalizing p with
  | zero => simpa only [coreTime, Nat.zero_add, Nat.one_mul] using hB
  | succ f ih =>
      rw [coreTime]
      by_cases h : k ≤ p
      · rw [ite_eq_left h]
        have hp := prefixTime_le_roundBudget g k p
        have hm := Nat.mul_le_mul_left (f + 1) hB
        have hc : f + 2 ≤ (f + 1) * roundBudget g k := by omega
        calc
          prefixTime k p + (f + 2) ≤ roundBudget g k + (f + 1) * roundBudget g k :=
            Nat.add_le_add hp hc
          _ = (f + 1 + 1) * roundBudget g k := by ring
      · rw [ite_eq_right h]
        have hb := continuingTime_le g k p (by omega)
        have hr := ih (p * g)
        calc
          prefixTime k p + ((p + g * p + 2) + coreTime g k f (p * g)) =
              (prefixTime k p + (p + g * p + 2)) + coreTime g k f (p * g) := by omega
          _ ≤ roundBudget g k + (f + 1) * roundBudget g k := Nat.add_le_add hb hr
          _ = (f + 1 + 1) * roundBudget g k := by ring

theorem initStep (g k : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩ =
      some ⟨some .fuelFirst, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] []⟩ := by
  change some (TM2.stepAux (program g .init) _ _) = _
  simp [program, TM2.stepAux, memory, encodeWord]

def totalTime (g k : Nat) : Nat := 1 + 2 * (k + 2) + coreTime g k k 1

/-- Initialization writes one and zero, copies the actual input to the fuel
tape, and executes the proved loop. All auxiliary tapes are empty on exit. -/
theorem searchTrace (g k : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[totalTime g k]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) []
          (encodeWord (PreprocessingLevels.levelLoop g k k 0 1).2) []
          (encodeWord (PreprocessingLevels.levelLoop g k k 0 1).1) [] [] []⟩ := by
  have hi : (advance (TM2.step (program g)))^[1]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨some .fuelFirst, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] []⟩ :=
    initStep g k ambient register
  have hc := MachineCopy.copyTrace Tape.input Tape.fuel Tape.spare
    (by decide) (by decide) (by decide) false Label.fuelFirst Label.fuelSecond
    (some Label.guard) (program g) rfl rfl
    (memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] [])
    rfl (ambient, false) register
  simp only [memory, encodeWord_length, List.append_nil, update_fuel] at hc
  exact appendTrace_inline_MachineCeilingPower _ (appendTrace_inline_MachineCeilingPower _ hi hc) (coreTrace g k k 0 1 ambient none)

def timeBound (g k : Nat) : Nat := (g + 8) * (k + 1) ^ 2 + 18 * (k + 1) + 3

theorem totalTime_le (g k : Nat) : totalTime g k ≤ timeBound g k := by
  have h := coreTime_le g k k 1
  calc
    totalTime g k ≤ 1 + 2 * (k + 2) + (k + 1) * roundBudget g k :=
      Nat.add_le_add_left h _
    _ = timeBound g k := by unfold roundBudget timeBound; ring

/-- The bound is one fixed quadratic polynomial in the actual unary input
length. Its coefficient may depend on the fixed growth factor. -/
noncomputable def timePolynomial (g : Nat) : Polynomial Nat :=
  Polynomial.C (g + 8) * Polynomial.X ^ 2 + 18 * Polynomial.X + 3

theorem timePolynomial_encoding (g k : Nat) :
    (timePolynomial g).eval (encodeWord k).length = timeBound g k := by
  simp [timePolynomial, timeBound, encodeWord_length]

/-- Instantiate the fixed program with the actual expander growth. This is
the exact executable result already identified with the ceiling logarithm. -/
theorem paddingTrace (k : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program ExpanderFamily.growth)))^[totalTime ExpanderFamily.growth k]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (PreprocessingLevels.paddedSize k)) []
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] [] []⟩ := by
  exact searchTrace ExpanderFamily.growth k ambient register

def paddingInTime (k : Nat) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program ExpanderFamily.growth))
      ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩
      (some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (PreprocessingLevels.paddedSize k)) []
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] [] []⟩)
      ((timePolynomial ExpanderFamily.growth).eval (encodeWord k).length) where
  steps := totalTime ExpanderFamily.growth k
  evals_in_steps := paddingTrace k ambient register
  steps_le_m := by rw [timePolynomial_encoding]; exact totalTime_le _ _

theorem paddingOutput_bounds (k : Nat) :
    PreprocessingLevels.boundedLevel k ≤ k ∧
      k ≤ PreprocessingLevels.paddedSize k ∧
      PreprocessingLevels.paddedSize k ≤ ExpanderFamily.growth * (k + 1) := by
  refine ⟨PreprocessingLevels.boundedLevel_le_input k, PreprocessingLevels.le_paddedSize k, ?_⟩
  by_cases hk : k = 0
  · subst k
    simpa using ExpanderFamily.growth_gt_one.le
  · exact (PreprocessingLevels.paddedSize_bounds (Nat.pos_of_ne_zero hk)).2.trans
      (Nat.mul_le_mul_left ExpanderFamily.growth (Nat.le_succ k))

end MaxCutGames.Foundations.Complexity.MachineCeilingPower

end OAI
