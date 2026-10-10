import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.PCP.SourceLoopInitLemmas

namespace OAI

/-!
Physical postprocessing of the two-side address codec. The program reads
`2*C,q,m`, writes `C,q,m`, and replaces each row `u,C+v,table` by `u,v,table`.
Only the fixed alphabet size `q` occurs in finite control. All input-dependent
integers reside on unary tapes. Six Bool tapes suffice.
-/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitProgram

open Turing
open UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Hastad
open UniqueGamesTheorem.Reduction

inductive Tape
  | input | capacity | saved | remaining | accumulator | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .capacity, .saved, .remaining,
  .accumulator, .output]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State := Unit × Option Bool

def initialState : State := ((), none)

def clearKeys : List Tape := [.input, .capacity, .saved, .remaining]

inductive Label (q : Nat)
  | start | halfFirst | halfSecond | alphabet | count | guard
  | source | subtract | restore | target
  | table (completed : Fin (q + 1))
  | finishStart
  | finish (localLabel : SourceRuntimeFinish.Label clearKeys)
  deriving DecidableEq, Fintype

/-- Consume one complete unary field, including its delimiter, appending its
reverse to the output accumulator. All other tapes are unchanged. -/
def copyField {q : Nat} (loopLabel exitLabel : Label q) :
    TM2.Stmt (fun _ : Tape => Bool) (Label q) State :=
  .pop .input (fun state head => (state.1, head))
    (.push .accumulator (fun state => state.2.getD false)
      (.branch (fun state => state.2.getD false)
        (.goto fun _ => loopLabel)
        (.load (fun _ => initialState) (.goto fun _ => exitLabel))))

def program (q : Nat) : Label q → TM2.Stmt (fun _ : Tape => Bool) (Label q) State
  | .start => .push .capacity (fun _ => false)
      (.push .remaining (fun _ => false) (.goto fun _ => .halfFirst))
  | .halfFirst => .pop .input (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.goto fun _ => .halfSecond)
        (.push .accumulator (fun _ => false)
          (.load (fun _ => initialState) (.goto fun _ => .alphabet))))
  | .halfSecond => .pop .input (fun state _ => state)
      (.push .capacity (fun _ => true)
        (.push .accumulator (fun _ => true) (.goto fun _ => .halfFirst)))
  | .alphabet => copyField .alphabet .count
  | .count => .pop .input (fun state head => (state.1, head))
      (.push .accumulator (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false)
          (.push .remaining (fun _ => true) (.goto fun _ => .count))
          (.load (fun _ => initialState) (.goto fun _ => .guard))))
  | .guard => MachineUnaryCounter.guard .remaining .source .finishStart
  | .source => copyField .source .subtract
  | .subtract => .peek .capacity (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.pop .capacity (fun state _ => state)
          (.pop .input (fun state _ => state)
            (.push .saved (fun _ => true) (.goto fun _ => .subtract))))
        (.load (fun _ => initialState) (.goto fun _ => .restore)))
  | .restore => MachineTransfer.loopAt .saved .capacity id false .restore (some .target)
  | .target => copyField .target (.table 0)
  | .table completed =>
      if h : completed.val < q then
        copyField (.table completed) (.table ⟨completed.val + 1, by omega⟩)
      else .load (fun _ => initialState) (.goto fun _ => .guard)
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      () Label.finish none label

def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label q
  main := .start
  σ := State
  initialState := initialState
  m := program q

theorem finite_workAlphabet (q : Nat) (tape : (machine q).K) :
    Finite ((machine q).Γ tape) := by
  change Finite Bool
  infer_instance

theorem accumulator_not_mem_clearKeys : Tape.accumulator ∉ clearKeys := by decide
theorem output_not_mem_clearKeys : Tape.output ∉ clearKeys := by decide

theorem clearKeys_covers (tape : Tape) (ha : tape ≠ .accumulator)
    (ho : tape ≠ .output) : tape ∈ clearKeys := by
  cases tape <;> simp_all [clearKeys]

end UniqueGamesTheorem.Explicit.MachineSingleOrbitProgram

/-! Exact streaming traces in the single-orbit postprocessor. -/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitStreams

open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition MachineSingleOrbitProgram

def tapes (input capacity saved remaining accumulator output : List Bool) : Tape → List Bool
  | .input => input
  | .capacity => capacity
  | .saved => saved
  | .remaining => remaining
  | .accumulator => accumulator
  | .output => output

@[simp] theorem tapes_input (i c s r a o : List Bool) : tapes i c s r a o .input = i := rfl
@[simp] theorem tapes_capacity (i c s r a o : List Bool) : tapes i c s r a o .capacity = c := rfl
@[simp] theorem tapes_saved (i c s r a o : List Bool) : tapes i c s r a o .saved = s := rfl
@[simp] theorem tapes_remaining (i c s r a o : List Bool) : tapes i c s r a o .remaining = r := rfl
@[simp] theorem tapes_accumulator (i c s r a o : List Bool) : tapes i c s r a o .accumulator = a := rfl
@[simp] theorem tapes_output (i c s r a o : List Bool) : tapes i c s r a o .output = o := rfl

@[simp] theorem update_tapes (i c s r a o : List Bool) (t : Tape) (word : List Bool) :
    Function.update (tapes i c s r a o) t word =
      tapes (if t = .input then word else i) (if t = .capacity then word else c)
        (if t = .saved then word else s) (if t = .remaining then word else r)
        (if t = .accumulator then word else a) (if t = .output then word else o) := by
  cases t <;> funext k <;> cases k <;> simp [tapes]

def cfg {q : Nat} (label : Label q) (register : Option Bool)
    (i c s r a o : List Bool) : TM2.Cfg (fun _ : Tape => Bool) (Label q) State :=
  ⟨some label, ((), register), tapes i c s r a o⟩

theorem copyStep_true {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg loopLabel register (true :: i) c s r a o) =
      some (cfg loopLabel (some true) i c s r (true :: a) o) := by
  change some (TM2.stepAux (program q loopLabel) _ _) = _
  rw [atLoop]
  simp [copyField, TM2.stepAux, cfg]

theorem copyStep_false {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg loopLabel register (false :: i) c s r a o) =
      some (cfg exitLabel none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q loopLabel) _ _) = _
  rw [atLoop]
  simp [copyField, TM2.stepAux, cfg, initialState]

/-- The physical field copy takes one transition for each input bit. -/
theorem copyFieldTrace {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (n : Nat) (suffix c s r a o : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg loopLabel register (encodeWord n ++ suffix) c s r a o)) =
      some (cfg exitLabel none suffix c s r ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing a register with
  | zero =>
    simpa [encodeWord] using copyStep_false loopLabel exitLabel atLoop suffix c s r a o register
  | succ n ih =>
    have hw : encodeWord (n + 1) ++ suffix = true :: (encodeWord n ++ suffix) := by
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, Function.iterate_succ_apply, advance_some,
      copyStep_true loopLabel exitLabel atLoop, ih]
    congr 2
    simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

/-- All permutation fields are copied with a finite delimiter counter. -/
theorem tableTrace {q : Nat} (completed : Fin (q + 1)) (words : List Nat)
    (hcount : completed.val + words.length = q)
    (suffix c s r a o : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[(encodeWords words).length + 1]
      (some (cfg (.table completed) register (encodeWords words ++ suffix) c s r a o)) =
      some (cfg .guard none suffix c s r ((encodeWords words).reverse ++ a) o) := by
  induction words generalizing completed a register with
  | nil =>
    have hc : ¬ completed.val < q := by simp only [List.length_nil] at hcount; omega
    change some (TM2.stepAux (program q (.table completed)) _ _) = _
    simp [program, hc, TM2.stepAux, cfg, initialState, encodeWords]
  | cons n words ih =>
    have hc : completed.val < q := by simp only [List.length_cons] at hcount; omega
    let next : Fin (q + 1) := ⟨completed.val + 1, by omega⟩
    have hn : next.val + words.length = q := by
      simp only [List.length_cons] at hcount
      dsimp [next]
      omega
    have hp : program q (.table completed) = copyField (.table completed) (.table next) := by
      simp [program, hc, next]
    have first := copyFieldTrace (.table completed) (.table next) hp n
      (encodeWords words ++ suffix) c s r a o register
    have rest := ih next hn ((encodeWord n).reverse ++ a) none
    have ht : (encodeWords (n :: words)).length + 1 =
        ((encodeWords words).length + 1) + (n + 1) := by
      simp only [encodeWords, List.length_append, encodeWord_length]
      omega
    rw [ht, Function.iterate_add_apply]
    simp only [encodeWords, List.append_assoc]
    rw [first, rest]
    simp only [List.reverse_append, List.append_assoc]

end UniqueGamesTheorem.Explicit.MachineSingleOrbitStreams

/-! Physical unary header conversion, with an exact TM2 transition count. -/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitHeader

open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

theorem halfStep_first {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfFirst register (true :: i) c s r a o) =
      some (cfg .halfSecond (some true) i c s r a o) := by
  change some (TM2.stepAux (program q .halfFirst) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem halfStep_second {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfSecond register (true :: i) c s r a o) =
      some (cfg .halfFirst register i (true :: c) s r (true :: a) o) := by
  change some (TM2.stepAux (program q .halfSecond) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem halfStep_false {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfFirst register (false :: i) c s r a o) =
      some (cfg .alphabet none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q .halfFirst) _ _) = _
  simp [program, TM2.stepAux, cfg, initialState]

/-- Consume two unary input marks per output mark, storing the new capacity. -/
theorem halfTrace {q : Nat} (n : Nat) (suffix c s r a o : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[2 * n + 1]
      (some (cfg .halfFirst register (encodeWord (2 * n) ++ suffix) c s r a o)) =
      some (cfg .alphabet none suffix (List.replicate n true ++ c) s r
        ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing c a register with
  | zero =>
    simpa [encodeWord] using halfStep_false suffix c s r a o register
  | succ n ih =>
    have ht : 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 := by omega
    have hw : encodeWord (2 * (n + 1)) ++ suffix =
        true :: true :: (encodeWord (2 * n) ++ suffix) := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, ht, Function.iterate_succ_apply, advance_some, halfStep_first,
      Function.iterate_succ_apply, advance_some, halfStep_second, ih]
    congr 2
    · simp only [List.replicate_succ', List.append_assoc, List.singleton_append]
    · simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

theorem countStep_true {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .count register (true :: i) c s r a o) =
      some (cfg .count (some true) i c s (true :: r) (true :: a) o) := by
  change some (TM2.stepAux (program q .count) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem countStep_false {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .count register (false :: i) c s r a o) =
      some (cfg .guard none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q .count) _ _) = _
  simp [program, TM2.stepAux, cfg, initialState]

/-- Copy the occurrence count while also storing its physical unary counter. -/
theorem countTrace {q : Nat} (n : Nat) (suffix c s r a o : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .count register (encodeWord n ++ suffix) c s r a o)) =
      some (cfg .guard none suffix c s (List.replicate n true ++ r)
        ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing r a register with
  | zero =>
    simpa [encodeWord] using countStep_false suffix c s r a o register
  | succ n ih =>
    have hw : encodeWord (n + 1) ++ suffix = true :: (encodeWord n ++ suffix) := by
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, Function.iterate_succ_apply, advance_some, countStep_true, ih]
    congr 2
    · simp only [List.replicate_succ', List.append_assoc, List.singleton_append]
    · simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

theorem initial_configuration (q : Nat) (input : List Bool) :
    initList (machine q) input = cfg .start none input [] [] [] [] [] := by
  have ht : (initList (machine q) input).stk = tapes input [] [] [] [] [] := by
    funext t
    (cases t <;> simp [initList, machine, tapes]); rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem initialStep (q : Nat) (input : List Bool) :
    TM2.step (program q) (initList (machine q) input) =
      some (cfg .halfFirst none input [false] [] [false] [] []) := by
  rw [initial_configuration]
  change some (TM2.stepAux (program q .start) _ _) = _
  simp [program, TM2.stepAux, cfg]

/-- Read `2*C,q,m`, write `C,q,m`, and leave the physical unary capacity and
occurrence counters ready for the row loop.  The bound counts real transitions. -/
theorem headerTrace (q C m : Nat) (suffix : List Bool) :
    (advance (TM2.step (program q)))^[2 * C + q + m + 4]
      (some (initList (machine q)
        (encodeWord (2 * C) ++ encodeWord q ++ encodeWord m ++ suffix))) =
      some (cfg .guard none suffix (encodeWord C) [] (encodeWord m)
        (encodeWords [C, q, m]).reverse []) := by
  let input := encodeWord (2 * C) ++ encodeWord q ++ encodeWord m ++ suffix
  have hfirst :
      (advance (TM2.step (program q)))^[(2 * C + 1) + 1]
        (some (initList (machine q) input)) =
        some (cfg .alphabet none (encodeWord q ++ encodeWord m ++ suffix)
          (encodeWord C) [] [false] (encodeWord C).reverse []) := by
    rw [Function.iterate_add_apply _ (2 * C + 1) 1, Function.iterate_one]
    erw [advance_some, initialStep]
    simpa only [input, encodeWord, List.append_nil, List.append_assoc] using
      halfTrace (q := q) C (encodeWord q ++ encodeWord m ++ suffix)
        [false] [] [false] [] [] none
  have hsecond :
      (advance (TM2.step (program q)))^[(q + 1) + ((2 * C + 1) + 1)]
        (some (initList (machine q) input)) =
        some (cfg .count none (encodeWord m ++ suffix) (encodeWord C) [] [false]
          ((encodeWord q).reverse ++ (encodeWord C).reverse) []) := by
    rw [Function.iterate_add_apply _ (q + 1) ((2 * C + 1) + 1), hfirst]
    simpa only [List.append_assoc] using
      copyFieldTrace (q := q) .alphabet .count rfl q (encodeWord m ++ suffix)
        (encodeWord C) [] [false] (encodeWord C).reverse [] none
  have ht : 2 * C + q + m + 4 = (m + 1) + ((q + 1) + ((2 * C + 1) + 1)) := by omega
  change (advance (TM2.step (program q)))^[2 * C + q + m + 4]
    (some (initList (machine q) input)) = _
  rw [ht, Function.iterate_add_apply _ (m + 1) ((q + 1) + ((2 * C + 1) + 1)), hsecond]
  have hlast := countTrace (q := q) m suffix (encodeWord C) [] [false]
    ((encodeWord q).reverse ++ (encodeWord C).reverse) [] none
  simpa [encodeWord, encodeWords, List.reverse_append, List.append_assoc] using hlast

end UniqueGamesTheorem.Explicit.MachineSingleOrbitHeader

/-! Actual subtraction of the right-side address offset, preserving the unary
capacity tape for every later edge. -/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitSubtract

open Turing UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Reduction
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

theorem subtractStep_zero (q : Nat) (suffix saved remaining accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .subtract register suffix (encodeWord 0) saved remaining accumulator output) =
      some (cfg .restore none suffix (encodeWord 0) saved remaining accumulator output) := by
  change some (TM2.stepAux (program q .subtract) _ _) = _
  simp [program, TM2.stepAux, cfg, encodeWord, initialState]

theorem subtractStep_succ (q n : Nat)
    (suffix saved remaining accumulator output : List Bool) (register : Option Bool) :
    TM2.step (program q)
      (cfg .subtract register (List.replicate (n + 1) true ++ suffix)
        (encodeWord (n + 1)) saved remaining accumulator output) =
      some (cfg .subtract (some true) (List.replicate n true ++ suffix)
        (encodeWord n) (true :: saved) remaining accumulator output) := by
  change some (TM2.stepAux (program q .subtract) _ _) = _
  simp [program, TM2.stepAux, cfg, encodeWord, List.replicate_succ]

/-- The scan consumes precisely the capacity prefix of the target field. -/
theorem subtractTrace (q n : Nat)
    (suffix saved remaining accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .subtract register (List.replicate n true ++ suffix)
        (encodeWord n) saved remaining accumulator output)) =
      some (cfg .restore none suffix (encodeWord 0)
        (List.replicate n true ++ saved) remaining accumulator output) := by
  induction n generalizing saved register with
  | zero =>
    simpa using subtractStep_zero q suffix saved remaining accumulator output register
  | succ n ih =>
    rw [Function.iterate_succ_apply, advance_some, subtractStep_succ, ih]
    congr 2
    simp [List.replicate_add, List.append_assoc]

theorem restore_tapes (suffix capacity saved remaining accumulator output newSaved newCapacity : List Bool) :
    MachineTransfer.tapesAt Tape.saved Tape.capacity
      (tapes suffix capacity saved remaining accumulator output) newSaved newCapacity =
      tapes suffix newCapacity newSaved remaining accumulator output := by
  simp [MachineTransfer.tapesAt]

/-- The real saved-prefix transfer restores `C`, empties scratch, and takes
`C + 1` transitions. -/
theorem restoreTrace (q n : Nat) (suffix remaining accumulator output : List Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .restore none suffix (encodeWord 0) (List.replicate n true)
        remaining accumulator output)) =
      some (cfg .target none suffix (encodeWord n) [] remaining accumulator output) := by
  have h := MachineTransfer.transferAt_fromTapes (Γ := fun _ : Tape => Bool) (σ := Unit)
    Tape.saved Tape.capacity (by decide) id false (Label.restore : Label q) (some .target)
    (program q) rfl (tapes suffix (encodeWord 0) (List.replicate n true)
      remaining accumulator output) () none
  have next_eq : MachineTransfer.nextAt Tape.capacity (program q) =
      advance (TM2.step (program q)) := rfl
  rw [next_eq] at h
  simpa only [cfg, restore_tapes,
    tapes_saved, tapes_capacity, List.length_replicate,
    List.reverse_replicate, List.map_id, encodeWord, List.replicate_zero,
    List.nil_append] using h

/-- The complete target-offset removal preserves every other tape. In
particular the capacity is reusable and the `v` field delimiter is untouched. -/
theorem removeOffsetTrace (q C v : Nat) (suffix remaining accumulator output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[2 * (C + 1)]
      (some (cfg .subtract register (encodeWord (C + v) ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .target none (encodeWord v ++ suffix) (encodeWord C)
        [] remaining accumulator output) := by
  have hw : encodeWord (C + v) ++ suffix =
      List.replicate C true ++ (encodeWord v ++ suffix) := by
    simp only [encodeWord, List.replicate_add, List.append_assoc]
  rw [hw, show 2 * (C + 1) = (C + 1) + (C + 1) by omega,
    Function.iterate_add_apply, subtractTrace]
  simp only [List.append_nil]
  exact restoreTrace q C (encodeWord v ++ suffix) remaining accumulator output

end UniqueGamesTheorem.Explicit.MachineSingleOrbitSubtract

/-! Complete ordered row traversal of the physical one-orbit postprocessor. -/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitRows

open Turing UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Target
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams
open MachineSingleOrbitSubtract MachineSingleOrbitCodec

theorem joinTrace {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (h : f^[m] x = y) (h' : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, h, h']

def rowCost {C q : Nat} (c : Constraint C q) : Nat :=
  (doubledRowBits c).length + C + 3

theorem rowTrace {C q : Nat} (c : Constraint C q)
    (suffix remaining accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[rowCost c]
      (some (cfg .source register (doubledRowBits c ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .guard none suffix (encodeWord C) [] remaining
        ((rowBits c).reverse ++ accumulator) output) := by
  let table := encodeWords (tableWords c.permutation)
  let afterSource := (encodeWord c.source.val).reverse ++ accumulator
  let afterTarget := (encodeWord c.target.val).reverse ++ afterSource
  have hs := copyFieldTrace (q := q) .source .subtract rfl c.source.val
    (encodeWord (C + c.target.val) ++ table ++ suffix)
    (encodeWord C) [] remaining accumulator output register
  have hd := removeOffsetTrace q C c.target.val (table ++ suffix)
    remaining afterSource output none
  have ht := copyFieldTrace (q := q) .target (.table 0) rfl c.target.val
    (table ++ suffix) (encodeWord C) [] remaining afterSource output none
  have hp := tableTrace (q := q) 0 (tableWords c.permutation)
    (by simp) suffix (encodeWord C) [] remaining afterTarget output none
  have hs' : (advance (TM2.step (program q)))^[c.source.val + 1]
      (some (cfg .source register (doubledRowBits c ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .subtract none (encodeWord (C + c.target.val) ++ (table ++ suffix))
        (encodeWord C) [] remaining afterSource output) := by
    simpa only [doubledRowBits_eq, List.append_assoc, afterSource, table] using hs
  have hsd := joinTrace hs' hd
  have hsdt := joinTrace hsd ht
  have hall := joinTrace hsdt hp
  have hcost : (encodeWords (tableWords c.permutation)).length + 1 +
        (c.target.val + 1 + (2 * (C + 1) + (c.source.val + 1))) = rowCost c := by
    simp only [rowCost, doubledRowBits_eq, List.length_append, encodeWord_length]
    omega
  rw [hcost] at hall
  simpa only [rowBits_eq, List.reverse_append, List.append_assoc,
    afterTarget, afterSource, table] using hall

theorem guardStep_succ (q n : Nat) (input capacity saved accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .guard register input capacity saved (encodeWord (n + 1)) accumulator output) =
      some (cfg .source none input capacity saved (encodeWord n) accumulator output) := by
  change some (TM2.stepAux (program q .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux, cfg, encodeWord, List.replicate_succ]

theorem guardStep_zero (q : Nat) (input capacity saved accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .guard register input capacity saved (encodeWord 0) accumulator output) =
      some (cfg .finishStart none input capacity saved (encodeWord 0) accumulator output) := by
  change some (TM2.stepAux (program q .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux, cfg, encodeWord]

def rowsCost {C q : Nat} (cs : List (Constraint C q)) : Nat :=
  (doubledRowsBits cs).length + (C + 4) * cs.length + 1

theorem rowsCost_cons {C q : Nat} (c : Constraint C q) (cs : List (Constraint C q)) :
    rowsCost (c :: cs) = rowsCost cs + rowCost c + 1 := by
  simp only [rowsCost, rowCost, doubledRowsBits_cons, List.length_append,
    List.length_cons, Nat.mul_add, Nat.mul_one]
  omega

/-- The actual counted loop visits every row once and preserves its order.
No complete-loop execution is supplied as an input hypothesis. -/
theorem rowsTrace {C q : Nat} (cs : List (Constraint C q))
    (suffix accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[rowsCost cs]
      (some (cfg .guard register (doubledRowsBits cs ++ suffix)
        (encodeWord C) [] (encodeWord cs.length) accumulator output)) =
      some (cfg .finishStart none suffix (encodeWord C) [] (encodeWord 0)
        ((rowsBits cs).reverse ++ accumulator) output) := by
  induction cs generalizing accumulator register with
  | nil =>
    simpa [rowsCost] using guardStep_zero q suffix (encodeWord C) [] accumulator output register
  | cons c cs ih =>
    have hg : (advance (TM2.step (program q)))^[1]
        (some (cfg .guard register (doubledRowsBits (c :: cs) ++ suffix)
          (encodeWord C) [] (encodeWord (c :: cs).length) accumulator output)) =
        some (cfg .source none (doubledRowBits c ++ (doubledRowsBits cs ++ suffix))
          (encodeWord C) [] (encodeWord cs.length) accumulator output) := by
      simpa only [Function.iterate_one, advance_some, List.length_cons,
        doubledRowsBits_cons, List.append_assoc] using
        guardStep_succ q cs.length (doubledRowsBits (c :: cs) ++ suffix)
          (encodeWord C) [] accumulator output register
    have hr := rowTrace c (doubledRowsBits cs ++ suffix) (encodeWord cs.length)
      accumulator output none
    have ht := ih ((rowBits c).reverse ++ accumulator) none
    have hall := joinTrace (joinTrace hg hr) ht
    have hcost : rowsCost cs + (rowCost c + 1) = rowsCost (c :: cs) := by
      rw [rowsCost_cons]
      omega
    rw [hcost] at hall
    simpa only [rowsBits_cons, List.reverse_append, List.append_assoc] using hall

end UniqueGamesTheorem.Explicit.MachineSingleOrbitRows

end OAI
