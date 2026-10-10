import Mathlib
import OAI.Computability.MaxCut.Machines.MachineCopy
import OAI.Computability.MaxCut.Machines.Machine

namespace OAI

/-!
Actual caller-program traces for non-destructive unary-prefix emission and
the two headers of the raw initial graph. Unread suffixes are never scanned.
-/

namespace MaxCutGames.Foundations.Complexity.MachineInitialHeaders

open Turing
open Reduction.MachineTransfer
open Reduction.MachineSubstitution
open MachineCopy

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def prefixScan (source scratch output : K) (scale : ℕ) (again restore : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push scratch (fun _ => true)
        (pushWord output (List.replicate scale true) (.goto fun _ => again)))
      (.branch (fun state => state.2.isSome)
        (.push source (fun _ => false)
          (.load (fun state => (state.1, none)) (.goto fun _ => restore)))
        (.load (fun state => (state.1, none)) (.goto fun _ => restore))))

private theorem update_source_inline_MachineInitialHeaders (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (base : K → List Bool) (input saved emitted replacement : List Bool) :
    Function.update (forkTapes source scratch output base input saved emitted)
      source replacement = forkTapes source scratch output base replacement saved emitted := by
  funext k
  by_cases hs : k = source
  · subst k; simp [forkTapes, hst, hso]
  · by_cases ht : k = scratch
    · subst k; simp [forkTapes, Ne.symm hst, hto]
    · by_cases ho : k = output
      · subst k; simp [forkTapes, Ne.symm hso]
      · simp [forkTapes, hs, ht, ho]

private theorem update_scratch_inline_MachineInitialHeaders (source scratch output : K) (hto : scratch ≠ output)
    (base : K → List Bool) (input saved emitted replacement : List Bool) :
    Function.update (forkTapes source scratch output base input saved emitted)
      scratch replacement = forkTapes source scratch output base input replacement emitted := by
  funext k
  by_cases ht : k = scratch
  · subst k; simp [forkTapes, hto]
  · by_cases ho : k = output
    · subst k; simp [forkTapes, Ne.symm hto]
    · simp [forkTapes, ht, ho]

private theorem update_output_inline_MachineInitialHeaders (source scratch output : K)
    (base : K → List Bool) (input saved emitted replacement : List Bool) :
    Function.update (forkTapes source scratch output base input saved emitted)
      output replacement = forkTapes source scratch output base input saved replacement := by
  simp [forkTapes]

theorem prefixStep_true (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ) (base : K → List Bool)
    (input saved emitted : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (prefixScan source scratch output scale again restore)
      (ambient, register) (forkTapes source scratch output base (true :: input) saved emitted) =
      ⟨some again, (ambient, some true), forkTapes source scratch output base input
        (true :: saved) (List.replicate scale true ++ emitted)⟩ := by
  simp [prefixScan, TM2.stepAux, hst, hso, hto, update_source_inline_MachineInitialHeaders, update_scratch_inline_MachineInitialHeaders,
    stepAux_pushWord, update_output_inline_MachineInitialHeaders]

theorem prefixStep_false (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ) (base : K → List Bool)
    (suffix saved emitted : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (prefixScan source scratch output scale again restore)
      (ambient, register) (forkTapes source scratch output base (false :: suffix) saved emitted) =
      ⟨some restore, (ambient, none),
        forkTapes source scratch output base (false :: suffix) saved emitted⟩ := by
  simp [prefixScan, TM2.stepAux, hst, hso, hto, update_source_inline_MachineInitialHeaders]

private theorem replicate_append_cons_inline_MachineInitialHeaders (n : ℕ) (xs : List Bool) :
    List.replicate n true ++ true :: xs = List.replicate (n + 1) true ++ xs := by
  rw [List.replicate_add]
  simp

/-- The first loop takes one transition per unary bit and one for the delimiter. -/
theorem prefixScanTrace (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program again = prefixScan source scratch output scale again restore)
    (base : K → List Bool) (n : ℕ) (suffix saved emitted : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, register),
        forkTapes source scratch output base (encodeWord n ++ suffix) saved emitted⟩) =
      some ⟨some restore, (ambient, none),
        forkTapes source scratch output base (false :: suffix)
          (List.replicate n true ++ saved) (List.replicate (scale * n) true ++ emitted)⟩ := by
  induction n generalizing saved emitted register with
  | zero =>
    simp only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      encodeWord, List.replicate_zero, List.nil_append, List.singleton_append,
      Nat.mul_zero]
    change some (TM2.stepAux (program again) _ _) = _
    rw [atScan, prefixStep_false source scratch output hst hso hto]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (some (TM2.stepAux (program again) _ _)) = _
    rw [atScan]
    simp only [encodeWord, List.replicate_succ, List.cons_append]
    rw [prefixStep_true source scratch output hst hso hto]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, some true),
        forkTapes source scratch output base (encodeWord n ++ suffix)
          (true :: saved) (List.replicate scale true ++ emitted)⟩) = _
    rw [ih]
    have hs : List.replicate n true ++ true :: saved =
        true :: (List.replicate n true ++ saved) := by
      rw [replicate_append_cons_inline_MachineInitialHeaders, List.replicate_succ, List.cons_append]
    simp only [hs, Nat.mul_succ, List.replicate_add, List.append_assoc]

theorem prefixTrace (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program again = prefixScan source scratch output scale again restore)
    (atRestore : program restore = loopAt scratch source id false restore exit)
    (base : K → List Bool) (n : ℕ) (suffix : List Bool)
    (hsource : base source = encodeWord n ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 2]
      (some ⟨some again, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Function.update base output
        (List.replicate (scale * n) true ++ base output)⟩ := by
  have scan := prefixScanTrace source scratch output hst hso hto scale again restore
    program atScan base n suffix [] (base output) ambient register
  have hstart : forkTapes source scratch output base (encodeWord n ++ suffix) []
      (base output) = base := by
    rw [← hsource, ← scratchEmpty]
    exact forkTapes_self source scratch output base
  rw [hstart] at scan
  simp only [List.append_nil] at scan
  let emitted := List.replicate (scale * n) true ++ base output
  let scanned := forkTapes source scratch output base (false :: suffix)
    (List.replicate n true) emitted
  have restoreTrace := transferAt_fromTapes scratch source (Ne.symm hst) id false
    restore exit program atRestore scanned ambient none
  change (MachineComposition.advance (TM2.step program))^[(scanned scratch).length + 1]
    (some ⟨some restore, (ambient, none), scanned⟩) = _ at restoreTrace
  have hs : scanned scratch = List.replicate n true := by simp [scanned, hto]
  have hi : scanned source = false :: suffix := by simp [scanned, hst, hso]
  rw [hs, hi] at restoreTrace
  simp only [List.length_replicate, List.reverse_replicate, List.map_id] at restoreTrace
  have hrestored : tapesAt scratch source scanned []
      (List.replicate n true ++ false :: suffix) = Function.update base output emitted := by
    funext k
    by_cases hks : k = source
    · subst k
      simp [tapesAt, hso, hsource, encodeWord]
    · by_cases hkt : k = scratch
      · subst k
        simp [tapesAt, Ne.symm hst, hto, scratchEmpty]
      · by_cases hko : k = output
        · subst k
          simp [tapesAt, scanned, forkTapes, Ne.symm hso, Ne.symm hto]
        · simp [tapesAt, scanned, forkTapes, hks, hkt, hko]
  rw [hrestored] at restoreTrace
  rw [show 2 * n + 2 = (n + 1) + (n + 1) by omega,
    Function.iterate_add_apply, scan]
  exact restoreTrace

def prefixInTime (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program again = prefixScan source scratch output scale again restore)
    (atRestore : program restore = loopAt scratch source id false restore exit)
    (base : K → List Bool) (n : ℕ) (suffix : List Bool)
    (hsource : base source = encodeWord n ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), Function.update base output
        (List.replicate (scale * n) true ++ base output)⟩) (2 * n + 2) where
  steps := 2 * n + 2
  evals_in_steps := prefixTrace source scratch output hst hso hto scale again restore exit
    program atScan atRestore base n suffix hsource scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

omit [DecidableEq K] in
theorem prefixScan_pushBound (source scratch output : K) (scale : ℕ) (again restore : Λ) :
    Runtime.statementPushBound (prefixScan (σ := σ) source scratch output scale again restore) =
      scale + 1 := by
  simp only [prefixScan, Runtime.statementPushBound, statementPushBound_pushWord,
    List.length_replicate]
  omega

/-- One transition emits a fixed literal word and enters the caller continuation. -/
theorem literalTrace (output : K) (word : List Bool) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabel : program label = pushWord output word (exitAt output exit))
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some label, (ambient, register), base⟩) =
      some ⟨exit, (ambient, register),
        Function.update base output (word.reverse ++ base output)⟩ := by
  simp only [Function.iterate_one, MachineComposition.advance_some]
  change some (TM2.stepAux (program label) _ _) = _
  rw [atLabel, stepAux_pushWord]
  cases exit <;> rfl

private theorem trace_trans_inline_MachineInitialHeaders {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

/-- The complete raw initial-graph header phase, in an arbitrary caller program.
Only the output tape changes; its old suffix is preserved verbatim. -/
theorem headerTrace (nTape mTape scratch output : K)
    (_hnm : nTape ≠ mTape) (hnt : nTape ≠ scratch) (hno : nTape ≠ output)
    (hmt : mTape ≠ scratch) (hmo : mTape ≠ output) (hto : scratch ≠ output)
    (scanN restoreN scanM1 restoreM1 closeFirst scanM6 restoreM6 closeSecond : Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScanN : program scanN = prefixScan nTape scratch output 1 scanN restoreN)
    (atRestoreN : program restoreN = loopAt scratch nTape id false restoreN (some scanM1))
    (atScanM1 : program scanM1 = prefixScan mTape scratch output 1 scanM1 restoreM1)
    (atRestoreM1 : program restoreM1 = loopAt scratch mTape id false restoreM1 (some closeFirst))
    (atCloseFirst : program closeFirst = pushWord output [true, false]
      (exitAt output (some scanM6)))
    (atScanM6 : program scanM6 = prefixScan mTape scratch output 6 scanM6 restoreM6)
    (atRestoreM6 : program restoreM6 = loopAt scratch mTape id false restoreM6 (some closeSecond))
    (atCloseSecond : program closeSecond = pushWord output [true, false] (exitAt output exit))
    (base : K → List Bool) (n m : ℕ) (nSuffix mSuffix : List Bool)
    (hn : base nTape = encodeWord n ++ nSuffix)
    (hm : base mTape = encodeWord m ++ mSuffix) (ht : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 4 * m + 8]
      (some ⟨some scanN, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Function.update base output
        ((encodeWords [n + m + 1, 6 * m + 1]).reverse ++ base output)⟩ := by
  let out1 := List.replicate n true ++ base output
  let out2 := List.replicate m true ++ out1
  let out3 := [false, true] ++ out2
  let out4 := List.replicate (6 * m) true ++ out3
  let out5 := [false, true] ++ out4
  let b1 := Function.update base output out1
  let b2 := Function.update base output out2
  let b3 := Function.update base output out3
  let b4 := Function.update base output out4
  let b5 := Function.update base output out5
  have first := prefixTrace nTape scratch output hnt hno hto 1 scanN restoreN
    (some scanM1) program atScanN atRestoreN base n nSuffix hn ht ambient register
  simp only [Nat.one_mul] at first
  change (MachineComposition.advance (TM2.step program))^[2 * n + 2]
    (some ⟨some scanN, (ambient, register), base⟩) =
    some ⟨some scanM1, (ambient, none), b1⟩ at first
  have second := prefixTrace mTape scratch output hmt hmo hto 1 scanM1 restoreM1
    (some closeFirst) program atScanM1 atRestoreM1 b1 m mSuffix
    (by simp [b1, hmo, hm]) (by simp [b1, hto, ht]) ambient none
  simp only [Nat.one_mul, b1, Function.update_self, Function.update_idem] at second
  change (MachineComposition.advance (TM2.step program))^[2 * m + 2]
    (some ⟨some scanM1, (ambient, none), b1⟩) =
    some ⟨some closeFirst, (ambient, none), b2⟩ at second
  have third := literalTrace output [true, false] closeFirst (some scanM6)
    program atCloseFirst b2 ambient none
  simp only [b2, Function.update_self, Function.update_idem] at third
  change (MachineComposition.advance (TM2.step program))^[1]
    (some ⟨some closeFirst, (ambient, none), b2⟩) =
    some ⟨some scanM6, (ambient, none), b3⟩ at third
  have fourth := prefixTrace mTape scratch output hmt hmo hto 6 scanM6 restoreM6
    (some closeSecond) program atScanM6 atRestoreM6 b3 m mSuffix
    (by simp [b3, hmo, hm]) (by simp [b3, hto, ht]) ambient none
  simp only [b3, Function.update_self, Function.update_idem] at fourth
  change (MachineComposition.advance (TM2.step program))^[2 * m + 2]
    (some ⟨some scanM6, (ambient, none), b3⟩) =
    some ⟨some closeSecond, (ambient, none), b4⟩ at fourth
  have fifth := literalTrace output [true, false] closeSecond exit
    program atCloseSecond b4 ambient none
  simp only [b4, Function.update_self, Function.update_idem] at fifth
  change (MachineComposition.advance (TM2.step program))^[1]
    (some ⟨some closeSecond, (ambient, none), b4⟩) =
    some ⟨exit, (ambient, none), b5⟩ at fifth
  have total := trace_trans_inline_MachineInitialHeaders _ (trace_trans_inline_MachineInitialHeaders _ (trace_trans_inline_MachineInitialHeaders _ (trace_trans_inline_MachineInitialHeaders _ first second)
    third) fourth) fifth
  have hsteps : (((2 * n + 2) + (2 * m + 2)) + 1 + (2 * m + 2)) + 1 =
      2 * n + 4 * m + 8 := by omega
  rw [hsteps] at total
  have hout : out5 = (encodeWords [n + m + 1, 6 * m + 1]).reverse ++ base output := by
    simp only [out5, out4, out3, out2, out1, encodeWords, encodeWord,
      List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil,
      List.append_nil, List.nil_append, List.append_assoc, List.singleton_append]
    rw [show n + m + 1 = 1 + m + n by omega,
      show 6 * m + 1 = 1 + 6 * m by omega]
    simp only [List.replicate_add, List.replicate_one, List.cons_append,
      List.nil_append, List.append_assoc]
  simpa only [b5, hout] using total

def headerInTime (nTape mTape scratch output : K)
    (hnm : nTape ≠ mTape) (hnt : nTape ≠ scratch) (hno : nTape ≠ output)
    (hmt : mTape ≠ scratch) (hmo : mTape ≠ output) (hto : scratch ≠ output)
    (scanN restoreN scanM1 restoreM1 closeFirst scanM6 restoreM6 closeSecond : Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScanN : program scanN = prefixScan nTape scratch output 1 scanN restoreN)
    (atRestoreN : program restoreN = loopAt scratch nTape id false restoreN (some scanM1))
    (atScanM1 : program scanM1 = prefixScan mTape scratch output 1 scanM1 restoreM1)
    (atRestoreM1 : program restoreM1 = loopAt scratch mTape id false restoreM1 (some closeFirst))
    (atCloseFirst : program closeFirst = pushWord output [true, false]
      (exitAt output (some scanM6)))
    (atScanM6 : program scanM6 = prefixScan mTape scratch output 6 scanM6 restoreM6)
    (atRestoreM6 : program restoreM6 = loopAt scratch mTape id false restoreM6 (some closeSecond))
    (atCloseSecond : program closeSecond = pushWord output [true, false] (exitAt output exit))
    (base : K → List Bool) (n m : ℕ) (nSuffix mSuffix : List Bool)
    (hn : base nTape = encodeWord n ++ nSuffix)
    (hm : base mTape = encodeWord m ++ mSuffix) (ht : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some scanN, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), Function.update base output
        ((encodeWords [n + m + 1, 6 * m + 1]).reverse ++ base output)⟩)
      (2 * n + 4 * m + 8) where
  steps := 2 * n + 4 * m + 8
  evals_in_steps := headerTrace nTape mTape scratch output hnm hnt hno hmt hmo hto
    scanN restoreN scanM1 restoreM1 closeFirst scanM6 restoreM6 closeSecond exit
    program atScanN atRestoreN atScanM1 atRestoreM1 atCloseFirst atScanM6 atRestoreM6
    atCloseSecond base n m nSuffix mSuffix hn hm ht ambient register
  steps_le_m := Nat.le_refl _

end MaxCutGames.Foundations.Complexity.MachineInitialHeaders

/-! A finite literal setup sequence. Its list is fixed with the machine; no
input word or unbounded address is stored in finite control. -/

namespace MaxCutGames.Explicit.MachineProductSeed

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer
open MaxCutGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

abbrev Command (K : Type) := K × List Bool
abbrev LocalLabel (_ : Command K) := Unit
abbrev Label (commands : List (Command K)) := MachineFiniteSequence.Label LocalLabel commands

def entry (commands : List (Command K)) (labels : Label commands → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry LocalLabel (fun _ => ()) commands labels exit

def localInstruction (command : Command K) (_ : Unit → Λ) (exit : Option Λ) (_ : Unit) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  pushWord command.1 command.2.reverse (exitAt command.1 exit)

def instruction (commands : List (Command K)) (labels : Label commands → Λ) (exit : Option Λ) :
    Label commands → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  MachineFiniteSequence.instruction LocalLabel (fun _ => ()) localInstruction commands labels exit

def result (command : Command K) (base : K → List Bool) : K → List Bool :=
  Function.update base command.1 (command.2 ++ base command.1)

def finalTapes (commands : List (Command K)) (base : K → List Bool) : K → List Bool :=
  MachineFiniteSequence.resultOf result commands base

@[simp] theorem sequence_steps (commands : List (Command K)) (base : K → List Bool) :
    MachineFiniteSequence.steps result (fun _ _ => 1) commands base = commands.length := by
  induction commands generalizing base with
  | nil => rfl
  | cons command commands ih =>
    simp only [MachineFiniteSequence.steps, ih, List.length_cons]
    omega

/-- Each literal has an actual one-transition trace in the ambient machine. -/
theorem seedTrace (commands : List (Command K)) (labels : Label commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction commands labels exit l)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[commands.length]
      (some ⟨entry commands labels exit, (ambient, register), base⟩) =
      some ⟨exit, (ambient, register), finalTapes commands base⟩ := by
  have h := MachineFiniteSequence.trace LocalLabel (fun _ => ()) localInstruction
    result (fun _ _ => 1) program (fun _ => True) (fun _ => (ambient, register)) id commands
    (by intros; trivial)
    (by
      intro command hc localLabels localExit atLocal tapes ht
      have h := MachineInitialHeaders.literalTrace command.1 command.2.reverse
        (localLabels ()) localExit program (atLocal ()) tapes ambient register
      simpa only [List.reverse_reverse, id_eq, result] using h)
    labels exit atLabels base trivial
  simpa only [sequence_steps, entry, finalTapes, id_eq] using h

theorem finalTapes_frame (commands : List (Command K)) (base : K → List Bool)
    (k : K) (outside : ∀ command ∈ commands, k ≠ command.1) :
    finalTapes commands base k = base k := by
  induction commands generalizing base with
  | nil => rfl
  | cons command commands ih =>
    change finalTapes commands (result command base) k = base k
    rw [ih _ (fun c hc => outside c (by simp [hc]))]
    exact Function.update_of_ne (outside command (by simp)) _ _

theorem finalTapes_field (commands : List (Command K))
    (nodup : (commands.map Prod.fst).Nodup) (base : K → List Bool)
    (command : Command K) (member : command ∈ commands) :
    finalTapes commands base command.1 = command.2 ++ base command.1 := by
  induction commands generalizing base with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at nodup
    rcases List.mem_cons.mp member with rfl | member
    · change finalTapes rest (result command base) command.1 = _
      rw [finalTapes_frame rest _ command.1]
      · simp [result]
      · intro c hc he
        exact nodup.1 (List.mem_map.mpr ⟨c, hc, he.symm⟩)
    · have ne : command.1 ≠ first.1 := by
        intro h
        exact nodup.1 (List.mem_map.mpr ⟨command, member, h⟩)
      change finalTapes rest (result first base) command.1 = _
      rw [ih nodup.2 _ member, result, Function.update_of_ne ne]

end MaxCutGames.Explicit.MachineProductSeed

/-! Generic placement of the odometer-digit initialization used in
`Hastad.SourceLoopInit`. This extracts its seed/copy/trim scheme from the
formula/header parser: the actual checked copy loop preserves the radix and
scratch, and a single positive-unary pop leaves the remaining count.
The finite program depends on the fixed digit width, not on the radix value. -/

namespace MaxCutGames.Foundations.Complexity.MachineOdometerInit
open Turing

inductive Tape (k : Nat)
  | radix | scratch | current (j : Fin k) | remaining (j : Fin k)
  deriving DecidableEq, Fintype

inductive Label (k : Nat)
  | seed (j : Fin k) | copyOut (j : Fin k) | copyBack (j : Fin k) | trim (j : Fin k)
  | done
  deriving DecidableEq, Fintype

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

def labelAt (labels : Label k → Λ) (r : Nat) : Λ :=
  if h : r < k then labels (.seed ⟨r,h⟩) else labels .done

/-- Place one of finitely many actual statements into an arbitrary ambient
Boolean-tape program, preserving the ambient state component. -/
def statement (tape : Tape k → K) (labels : Label k → Λ) (exit : Option Λ) :
    Label k → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .seed j => .push (tape (.current j)) (fun _ => false)
      (.goto (fun _ => labels (.copyOut j)))
  | .copyOut j => Reduction.MachineTransfer.loopAt (tape .radix) (tape .scratch)
      id false (labels (.copyOut j)) (some (labels (.copyBack j)))
  | .copyBack j => MachineCopy.forkLoop (tape .scratch) (tape .radix) (tape (.remaining j))
      false (labels (.copyBack j)) (some (labels (.trim j)))
  | .trim j => .pop (tape (.remaining j)) (fun state _ => state)
      (.goto (fun _ => labelAt labels (j.val+1)))
  | .done => .load (fun state => (state.1,none))
      (Reduction.MachineTransfer.exitAt (tape .radix) exit)

def digitOutput (tape : Tape k → K) (j : Fin k) (m : Nat) (base : K → List Bool) :
    K → List Bool :=
  Function.update (Function.update base (tape (.current j)) (encodeWord 0))
    (tape (.remaining j)) (encodeWord (m-1))

theorem digitOutput_frame (tape : Tape k → K) (j : Fin k) (m : Nat)
    (base : K → List Bool) (p : K) (hc : p ≠ tape (.current j))
    (hr : p ≠ tape (.remaining j)) : digitOutput tape j m base p = base p := by
  simp [digitOutput,hc,hr]

variable (tape : Tape k → K) (distinct : Function.Injective tape)
  (labels : Label k → Λ) (exit : Option Λ)
  (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
  (atProgram : ∀l, program (labels l) = statement tape labels exit l)

def digitInTime (j : Fin k) (m : Nat) (hm : 0 < m) (base : K → List Bool)
    (hradix : base (tape .radix) = encodeWord m)
    (hcurrent : base (tape (.current j)) = [])
    (hremaining : base (tape (.remaining j)) = [])
    (hscratch : base (tape .scratch) = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.seed j)),(ambient,none),base⟩
      (some ⟨some (labelAt labels (j.val+1)),(ambient,none),digitOutput tape j m base⟩)
      (2*m+6) := by
  have hrc : tape .radix ≠ tape (.current j) := distinct.ne (by simp)
  have hrr : tape .radix ≠ tape (.remaining j) := distinct.ne (by simp)
  have hrs : tape .radix ≠ tape .scratch := distinct.ne (by simp)
  have hsc : tape .scratch ≠ tape (.current j) := distinct.ne (by simp)
  have hrsc : tape (.remaining j) ≠ tape .scratch := distinct.ne (by simp)
  have hrcc : tape (.remaining j) ≠ tape (.current j) := distinct.ne (by simp)
  let seeded := Function.update base (tape (.current j)) (encodeWord 0)
  have seedRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.seed j)),(ambient,none),base⟩
      (some ⟨some (labels (.copyOut j)),(ambient,none),seeded⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_refl _ }
    change some (TM2.stepAux (program (labels (.seed j))) (ambient,none) base) = _
    rw [atProgram]
    simp [statement,TM2.stepAux,seeded,hcurrent,encodeWord]
  have copiedRun := MachineCopy.copyInTime (tape .radix) (tape (.remaining j)) (tape .scratch)
    hrr hrs hrsc false (labels (.copyOut j)) (labels (.copyBack j))
    (some (labels (.trim j))) program (atProgram (.copyOut j)) (atProgram (.copyBack j))
    seeded (by simpa [seeded,hsc] using hscratch) ambient none
  let copied := Function.update seeded (tape (.remaining j)) (encodeWord m)
  have he : Function.update seeded (tape (.remaining j))
      (seeded (tape .radix) ++ seeded (tape (.remaining j))) = copied := by
    simp [copied,seeded,hradix,hremaining,hrc,hrcc]
  rw [he] at copiedRun
  have trimRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.trim j)),(ambient,none),copied⟩
      (some ⟨some (labelAt labels (j.val+1)),(ambient,none),digitOutput tape j m base⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_refl _ }
    change some (TM2.stepAux (program (labels (.trim j))) (ambient,none) copied) = _
    have hm' : m = (m-1)+1 := by omega
    have tail : (encodeWord m).tail = encodeWord (m-1) := by
      conv_lhs => rw [hm']
      simp [encodeWord,List.replicate_succ]
    rw [atProgram]
    simp [statement,TM2.stepAux,copied,seeded,digitOutput,tail]
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ seedRun copiedRun) trimRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  have hs : seeded (tape .radix) = encodeWord m := by simpa [seeded,hrc] using hradix
  rw [hs,encodeWord_length]
  omega

def stageTapes (tape : Tape k → K) (m : Nat) (base : K → List Bool) : Nat → K → List Bool
  | 0 => base
  | r+1 => if h : r < k then digitOutput tape ⟨r,h⟩ m (stageTapes tape m base r)
      else stageTapes tape m base r

theorem stageTapes_frame (m : Nat) (base : K → List Bool) (r : Nat)
    (p : K) (hc : ∀j, p ≠ tape (.current j)) (hr : ∀j, p ≠ tape (.remaining j)) :
    stageTapes tape m base r p = base p := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [stageTapes]
    split
    · rw [digitOutput_frame _ _ _ _ _ (hc _) (hr _),ih]
    · exact ih

include distinct in
theorem stageTapes_current (m : Nat) (base : K → List Bool) (r : Nat) (j : Fin k) :
    stageTapes tape m base r (tape (.current j)) =
      if j.val < r then encodeWord 0 else base (tape (.current j)) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r,hr⟩ : Fin k)
      · subst j; simp [digitOutput,distinct.eq_iff]
      · rw [digitOutput_frame _ _ _ _ _
          (distinct.ne (by simpa using hj)) (distinct.ne (by simp)),ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r+1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r+1 := by omega
      simp only [hjr,hjr',ite_true]

include distinct in
theorem stageTapes_remaining (m : Nat) (base : K → List Bool) (r : Nat) (j : Fin k) :
    stageTapes tape m base r (tape (.remaining j)) =
      if j.val < r then encodeWord (m-1) else base (tape (.remaining j)) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r,hr⟩ : Fin k)
      · subst j; simp [digitOutput]
      · rw [digitOutput_frame _ _ _ _ _
          (distinct.ne (by simp)) (distinct.ne (by simpa using hj)),ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r+1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r+1 := by omega
      simp only [hjr,hjr',ite_true]

/-- Place the actual finite initialization prefix inside an ambient program. -/
def prefixInTime (m : Nat) (hm : 0 < m) (base : K → List Bool)
    (hradix : base (tape .radix) = encodeWord m)
    (hcurrent : ∀j, base (tape (.current j)) = [])
    (hremaining : ∀j, base (tape (.remaining j)) = [])
    (hscratch : base (tape .scratch) = []) (ambient : σ) (r : Nat) (hr : r ≤ k) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt labels 0),(ambient,none),base⟩
      (some ⟨some (labelAt labels r),(ambient,none),stageTapes tape m base r⟩)
      (r*(2*m+6)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hrk : r < k := by omega
    let j : Fin k := ⟨r,hrk⟩
    let before := stageTapes tape m base r
    have one := digitInTime tape distinct labels exit program atProgram j m hm before
      (by dsimp only [before]; rw [stageTapes_frame tape _ _ _ _
          (fun _ => distinct.ne (by simp)) (fun _ => distinct.ne (by simp))]; exact hradix)
      (by simp [before,stageTapes_current tape distinct,j,hcurrent])
      (by simp [before,stageTapes_remaining tape distinct,j,hremaining])
      (by dsimp only [before]; rw [stageTapes_frame tape _ _ _ _
          (fun _ => distinct.ne (by simp)) (fun _ => distinct.ne (by simp))]; exact hscratch)
      ambient
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt labels r),(ambient,none),before⟩
        (some ⟨some (labelAt labels (r+1)),(ambient,none),stageTapes tape m base (r+1)⟩)
        (2*m+6) := by
      simpa only [labelAt,dite_eq_left hrk,j,stageTapes,before] using one
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (ih (by omega)) one'
    simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm] using joined

/-- Complete actual initialization, including width zero and the optional
continuation. The radix, scratch, ambient state and unrelated tapes survive. -/
def initializeInTime (m : Nat) (hm : 0 < m) (base : K → List Bool)
    (hradix : base (tape .radix) = encodeWord m)
    (hcurrent : ∀j, base (tape (.current j)) = [])
    (hremaining : ∀j, base (tape (.remaining j)) = [])
    (hscratch : base (tape .scratch) = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt labels 0),(ambient,none),base⟩
      (some ⟨exit,(ambient,none),stageTapes tape m base k⟩)
      (k*(2*m+6)+1) := by
  have initializedPrefix := prefixInTime tape distinct labels exit program atProgram m hm base
    hradix hcurrent hremaining hscratch ambient k (le_refl _)
  have doneRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt labels k),(ambient,none),stageTapes tape m base k⟩
      (some ⟨exit,(ambient,none),stageTapes tape m base k⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_refl _ }
    change some (TM2.stepAux (program (labelAt labels k)) (ambient,none) _) = _
    simp only [labelAt,Nat.lt_irrefl,↓reduceDIte]
    rw [atProgram]
    cases exit <;> rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ initializedPrefix doneRun

include distinct in
theorem output_current (m : Nat) (base : K → List Bool) (j : Fin k) :
    stageTapes tape m base k (tape (.current j)) = encodeWord 0 := by
  rw [stageTapes_current tape distinct]
  exact ite_eq_left j.isLt

include distinct in
theorem output_remaining (m : Nat) (base : K → List Bool) (j : Fin k) :
    stageTapes tape m base k (tape (.remaining j)) = encodeWord (m-1) := by
  rw [stageTapes_remaining tape distinct]
  exact ite_eq_left j.isLt

include distinct in
theorem output_radix (m : Nat) (base : K → List Bool) :
    stageTapes tape m base k (tape .radix) = base (tape .radix) :=
  stageTapes_frame tape m base k _
    (fun _ => distinct.ne (by simp)) (fun _ => distinct.ne (by simp))

include distinct in
theorem output_scratch (m : Nat) (base : K → List Bool) :
    stageTapes tape m base k (tape .scratch) = base (tape .scratch) :=
  stageTapes_frame tape m base k _
    (fun _ => distinct.ne (by simp)) (fun _ => distinct.ne (by simp))

end MaxCutGames.Foundations.Complexity.MachineOdometerInit

end OAI
