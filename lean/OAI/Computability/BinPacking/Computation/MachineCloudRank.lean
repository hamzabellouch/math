import OAI.Computability.BinPacking.Computation.PoweringMasterState
import OAI.Computability.BinPacking.PCP.PreprocessingRegularSoundness

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineCloudCount

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

open BinPackingGames.Foundations.PCP

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

end BinPackingGames.Foundations.Complexity.MachineCloudCount

namespace BinPackingGames.Foundations.Complexity.MachineCloudRank

open Turing MachineComposition MachineCloudCount

variable {σ : Type}

@[simp] theorem update_memory_spare (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .spare x = memory a b c d e x := by
  funext k
  cases k <;> rfl

inductive RankLabel
  | queryFirst | querySecond | querySkip | tableFirst | tableSecond
  | headerFirst | headerSecond | row | field | restore | done
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def rankSkip (i : Nat) : RankLabel :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .row

def rankProgram : RankLabel → TM2.Stmt Alphabet RankLabel (State σ)
  | .queryFirst => Reduction.MachineTransfer.loopAt
      .target .scratch id false .queryFirst (some .querySecond)
  | .querySecond => MachineCopy.forkLoop
      .scratch .target .spare false .querySecond (some .querySkip)
  | .querySkip => MachineLookup.discard .spare .querySkip .tableFirst
  | .tableFirst => Reduction.MachineTransfer.loopAt
      .original .scratch id false .tableFirst (some .tableSecond)
  | .tableSecond => MachineCopy.forkLoop
      .scratch .original .work false .tableSecond (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .row
  | .row => MachineUnaryCounter.guard .spare .field .done
  | .field => fieldLoop .field .restore
  | .restore => Reduction.MachineTransfer.loopAt
      .scratch .target id false .restore (some (rankSkip 0))
  | .skip i => MachineLookup.discard .work (.skip i) (rankSkip (i.val + 1))
  | .done => .halt

theorem rankProgram_skip {i : Nat} (hi : i < 4097) :
    rankProgram (σ := σ) (rankSkip i) =
      MachineLookup.discard .work (rankSkip i) (rankSkip (i + 1)) := by
  simp only [rankSkip, dite_eq_left hi, rankProgram]

theorem rowGuard_succ (original work target scratch count fuelSuffix : List Bool)
    (k : Nat) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (rankProgram (σ := σ))
      ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord (k + 1) ++ fuelSuffix)⟩ =
      some ⟨some .field, ((ambient, flag), none),
        memory original work target scratch count (encodeWord k ++ fuelSuffix)⟩ := by
  change some (TM2.stepAux (rankProgram .row) _ _) = _
  simp [rankProgram, MachineUnaryCounter.guard, TM2.stepAux, encodeWord,
    List.replicate_succ]

theorem rowGuard_zero (original work target scratch count fuelSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (rankProgram (σ := σ))
      ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ =
      some ⟨some .done, ((ambient, flag), none),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ := rfl

theorem zeroRowsTrace (original work target scratch count fuelSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[2]
      (some ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩) =
      some ⟨none, ((ambient, flag), none),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ := by
  rw [Function.iterate_succ_apply]
  change advance (TM2.step (rankProgram (σ := σ)))
    (TM2.step rankProgram ⟨some .row, ((ambient, flag), register),
      memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩) = _
  rw [rowGuard_zero]
  rfl

theorem rankRowTrace (r : Row) (hwidth : r.2.length = 4097) (v k : Nat)
    (original suffix targetSuffix fuelSuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[rowTime v r]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
          [] count (encodeWord (k + 1) ++ fuelSuffix)⟩) =
      some ⟨some .row, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if r.1 = v then 1 else 0) true ++ count)
          (encodeWord k ++ fuelSuffix)⟩ := by
  have hfield := preservingFieldTrace RankLabel.field RankLabel.restore (rankSkip 0)
    rankProgram rfl rfl original (encodeWords r.2 ++ suffix) targetSuffix count
    (encodeWord k ++ fuelSuffix) r.1 v ambient none
  have hskip := discardFieldsTrace rankSkip (rankProgram (σ := σ)) r.2 0
    (by intro i hi; simpa only [Nat.zero_add] using rankProgram_skip (hwidth ▸ hi))
    original suffix (encodeWord v ++ targetSuffix) []
    (List.replicate (if r.1 = v then 1 else 0) true ++ count)
    (encodeWord k ++ fuelSuffix) ambient false none
  have hnonempty : r.2 ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, rankSkip, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false] at hskip
  have htime : rowTime v r = (encodeWords r.2).length + (r.1 + min r.1 v + 2) + 1 := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [htime, Function.iterate_succ_apply]
  change (advance (TM2.step (rankProgram (σ := σ))))^[
      (encodeWords r.2).length + (r.1 + min r.1 v + 2)]
    (TM2.step rankProgram ⟨some .row, ((ambient, false), register),
      memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
        [] count (encodeWord (k + 1) ++ fuelSuffix)⟩) = _
  rw [rowGuard_succ, Function.iterate_add_apply]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hfield]
  exact hskip

def prefixTime (v : Nat) : List Row → Nat
  | [] => 2
  | r :: rs => prefixTime v rs + rowTime v r

theorem prefixTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097) (v : Nat)
    (original suffix targetSuffix fuelSuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[prefixTime v rs]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rs.flatMap rowWords) ++ suffix)
          (encodeWord v ++ targetSuffix) [] count (encodeWord rs.length ++ fuelSuffix)⟩) =
      some ⟨none, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) (encodeWord 0 ++ fuelSuffix)⟩ := by
  induction rs generalizing count register with
  | nil =>
      simpa only [prefixTime, List.flatMap_nil, encodeWords, List.nil_append,
        List.length_nil, rowsHits, List.replicate_zero] using
        zeroRowsTrace original suffix (encodeWord v ++ targetSuffix) [] count fuelSuffix
          ambient false register
  | cons r rs ih =>
      have hrow := rankRowTrace r (hwidth r (by simp)) v rs.length original
        (encodeWords (rs.flatMap rowWords) ++ suffix) targetSuffix fuelSuffix count ambient register
      have hrest := ih (by intro x hx; exact hwidth x (by simp [hx]))
        (List.replicate (if r.1 = v then 1 else 0) true ++ count) none
      simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.append_assoc,
        List.length_cons]
      rw [Function.iterate_add_apply, hrow]
      simpa only [rowsHits, ← List.append_assoc, List.replicate_append_replicate,
        Nat.add_comm] using hrest

theorem prefixTime_le (v : Nat) (rs : List Row) :
    prefixTime v rs ≤ 3 * (encodeWords (rs.flatMap rowWords)).length + 2 := by
  induction rs with
  | nil => simp only [prefixTime, List.flatMap_nil, encodeWords, List.length_nil,
      Nat.mul_zero, Nat.zero_add, le_refl]
  | cons r rs ih =>
      have hr := rowTime_le v r
      simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.length_append]
      omega

def queryWord (v k : Nat) (suffix : List Bool) : List Bool :=
  encodeWord v ++ (encodeWord k ++ suffix)

theorem encoded_rows_split (rs : List Row) (k : Nat) :
    encodeWords (rs.flatMap rowWords) =
      encodeWords ((rs.take k).flatMap rowWords) ++
        encodeWords ((rs.drop k).flatMap rowWords) := by
  have h := congrArg (fun xs : List Row => encodeWords (xs.flatMap rowWords))
    (List.take_append_drop k rs)
  simpa only [List.flatMap_append, encodeWords_append] using h.symm

def rankSteps (n m v k : Nat) (rs : List Row) (querySuffix : List Bool) : Nat :=
  2 * ((queryWord v k querySuffix).length + 1) + (v + 1) +
    2 * ((inputWord n m rs).length + 1) + (n + 1) + (m + 1) +
      prefixTime v (rs.take k)

theorem rankTrace (n m v k : Nat) (rs : List Row) (hk : k ≤ rs.length)
    (hwidth : ∀ r ∈ rs, r.2.length = 4097) (querySuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[rankSteps n m v k rs querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (inputWord n m rs) (encodeWords ((rs.drop k).flatMap rowWords))
          (queryWord v k querySuffix) []
          (List.replicate (rowsHits v (rs.take k)) true ++ count)
          (encodeWord 0 ++ querySuffix)⟩ := by
  have hquery := MachineCopy.copyTrace Tape.target Tape.spare Tape.scratch
    (by decide) (by decide) (by decide) false RankLabel.queryFirst RankLabel.querySecond
    (some RankLabel.querySkip) rankProgram rfl rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count [])
    rfl (ambient, false) register
  simp only [memory_target, memory_spare, List.append_nil, update_memory_spare] at hquery
  have hquerySkip := MachineLookup.discardTrace Tape.spare RankLabel.querySkip RankLabel.tableFirst
    rankProgram rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count (queryWord v k querySuffix))
    v (encodeWord k ++ querySuffix) rfl (ambient, false) none
  simp only [update_memory_spare] at hquerySkip
  have hcopy := MachineCopy.copyTrace Tape.original Tape.work Tape.scratch
    (by decide) (by decide) (by decide) false RankLabel.tableFirst RankLabel.tableSecond
    (some RankLabel.headerFirst) rankProgram rfl rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count
      (encodeWord k ++ querySuffix)) rfl (ambient, false) none
  simp only [memory_original, memory_work, List.append_nil, update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace Tape.work RankLabel.headerFirst RankLabel.headerSecond
    rankProgram rfl
    (memory (inputWord n m rs) (inputWord n m rs) (queryWord v k querySuffix) [] count
      (encodeWord k ++ querySuffix))
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (inputWord_eq n m rs) (ambient, false) none
  simp only [update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace Tape.work RankLabel.headerSecond RankLabel.row
    rankProgram rfl
    (memory (inputWord n m rs) (encodeWord m ++ encodeWords (rs.flatMap rowWords))
      (queryWord v k querySuffix) [] count (encodeWord k ++ querySuffix))
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [update_memory_work] at hsecond
  have hprefix := prefixTrace (rs.take k)
    (by intro r hr; exact hwidth r (List.mem_of_mem_take hr)) v
    (inputWord n m rs) (encodeWords ((rs.drop k).flatMap rowWords))
    (encodeWord k ++ querySuffix) querySuffix count ambient none
  have htake : (rs.take k).length = k := by
    simp only [List.length_take, Nat.min_eq_left hk]
  rw [htake, ← encoded_rows_split rs k] at hprefix
  rw [show rankSteps n m v k rs querySuffix = prefixTime v (rs.take k) +
      ((m + 1) + ((n + 1) + (2 * ((inputWord n m rs).length + 1) +
        ((v + 1) + 2 * ((queryWord v k querySuffix).length + 1))))) by
      unfold rankSteps; omega,
    Function.iterate_add_apply _ (prefixTime v (rs.take k)),
    Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
    Function.iterate_add_apply _ (2 * ((inputWord n m rs).length + 1)),
    Function.iterate_add_apply _ (v + 1), hquery, hquerySkip, hcopy, hfirst, hsecond]
  exact hprefix

theorem rankSteps_le (n m v k : Nat) (rs : List Row) (querySuffix : List Bool) :
    rankSteps n m v k rs querySuffix ≤
      5 * (inputWord n m rs).length + 3 * (queryWord v k querySuffix).length + 6 := by
  have hprefix := prefixTime_le v (rs.take k)
  have hsplit := congrArg List.length (encoded_rows_split rs k)
  simp only [List.length_append] at hsplit
  have hinput := inputWord_length n m rs
  have hquery : v + 1 ≤ (queryWord v k querySuffix).length := by
    simp only [queryWord, List.length_append, encodeWord_length]
    omega
  unfold rankSteps
  omega

theorem idxOf_filter_prefix {α : Type*} [BEq α] [LawfulBEq α]
    (p : α → Bool) (a : α) (hp : p a = true) :
    ∀ xs : List α, a ∈ xs →
      (xs.filter p).idxOf a = ((xs.take (xs.idxOf a)).filter p).length := by
  classical
  intro xs
  induction xs with
  | nil => intro ha; simp at ha
  | cons b xs ih =>
      intro ha
      by_cases hba : b = a
      · subst b
        simp [hp]
      · have ha' : a ∈ xs := by simpa [hba, Ne.symm hba] using ha
        cases hb : p b <;>
          simp [hba, hb, ih ha']

open BinPackingGames.Foundations.PCP

theorem tableRows_length (t : GraphTables.Table) : (tableRows t).length = t.darts := by
  simp only [tableRows, List.length_map, GraphTables.rowList_length]

theorem cloudRank_eq_prefix_count (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) :
    (PreprocessingCloudIndex.cloudRank t v e).val =
      rowsHits v.val ((tableRows t).take e.val.val) := by
  have hindex := idxOf_filter_prefix (fun x : Fin t.darts => decide (t.rows[x].tail = v))
    e.val (by simpa using e.property) (List.finRange t.darts) (List.mem_finRange e.val)
  simp only [List.idxOf_finRange] at hindex
  change (PreprocessingCloudIndex.cloudDarts t v).idxOf e.val = _
  unfold PreprocessingCloudIndex.cloudDarts
  rw [hindex, rowsHits_eq_filter]
  simp only [tableRows, rowList_eq_finRange_map, ← List.map_take, List.filter_map,
    List.length_map, Function.comp_def, Fin.val_inj]

theorem cloudRankTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v)
    (querySuffix countSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[
        rankSteps t.vertices t.darts v.val e.val.val (tableRows t) querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        memory (GraphTables.tableBits t) [] (queryWord v.val e.val.val querySuffix) []
          (encodeWord 0 ++ countSuffix) []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t)
          (encodeWords (((tableRows t).drop e.val.val).flatMap rowWords))
          (queryWord v.val e.val.val querySuffix) []
          (encodeWord (PreprocessingCloudIndex.cloudRank t v e).val ++ countSuffix)
          (encodeWord 0 ++ querySuffix)⟩ := by
  have hk : e.val.val ≤ (tableRows t).length := by
    rw [tableRows_length]
    exact e.val.isLt.le
  have h := rankTrace t.vertices t.darts v.val e.val.val (tableRows t) hk
    (tableRows_width t) querySuffix (encodeWord 0 ++ countSuffix) ambient register
  rw [tableRows_input, ← cloudRank_eq_prefix_count t v e, ← List.append_assoc,
    replicate_encodeWord, Nat.add_zero] at h
  exact h

def cloudRankInTime (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v)
    (querySuffix countSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (rankProgram (σ := σ)))
      ⟨some .queryFirst, ((ambient, false), register),
        memory (GraphTables.tableBits t) [] (queryWord v.val e.val.val querySuffix) []
          (encodeWord 0 ++ countSuffix) []⟩
      (some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t)
          (encodeWords (((tableRows t).drop e.val.val).flatMap rowWords))
          (queryWord v.val e.val.val querySuffix) []
          (encodeWord (PreprocessingCloudIndex.cloudRank t v e).val ++ countSuffix)
          (encodeWord 0 ++ querySuffix)⟩)
      (5 * (GraphTables.tableBits t).length +
        3 * (queryWord v.val e.val.val querySuffix).length + 6) where
  steps := rankSteps t.vertices t.darts v.val e.val.val (tableRows t) querySuffix
  evals_in_steps := cloudRankTrace t v e querySuffix countSuffix ambient register
  steps_le_m := by
    simpa only [tableRows_input] using
      rankSteps_le t.vertices t.darts v.val e.val.val (tableRows t) querySuffix

end BinPackingGames.Foundations.Complexity.MachineCloudRank

end OAI
