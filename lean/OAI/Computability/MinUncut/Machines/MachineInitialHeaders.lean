import Mathlib
import OAI.Computability.MinUncut.PCP.RawInitialPredicate

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineInitialHeaders

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

theorem update_source (source scratch output : K)
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

private theorem update_scratch (source scratch output : K) (hto : scratch ≠ output)
    (base : K → List Bool) (input saved emitted replacement : List Bool) :
    Function.update (forkTapes source scratch output base input saved emitted)
      scratch replacement = forkTapes source scratch output base input replacement emitted := by
  funext k
  by_cases ht : k = scratch
  · subst k; simp [forkTapes, hto]
  · by_cases ho : k = output
    · subst k; simp [forkTapes, Ne.symm hto]
    · simp [forkTapes, ht, ho]

theorem update_output (source scratch output : K)
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
  simp [prefixScan, TM2.stepAux, hst, hso, hto, update_source, update_scratch,
    stepAux_pushWord, update_output]

theorem prefixStep_false (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ) (base : K → List Bool)
    (suffix saved emitted : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (prefixScan source scratch output scale again restore)
      (ambient, register) (forkTapes source scratch output base (false :: suffix) saved emitted) =
      ⟨some restore, (ambient, none),
        forkTapes source scratch output base (false :: suffix) saved emitted⟩ := by
  simp [prefixScan, TM2.stepAux, hst, hso, hto, update_source]

private theorem replicate_append_cons (n : ℕ) (xs : List Bool) :
    List.replicate n true ++ true :: xs = List.replicate (n + 1) true ++ xs := by
  rw [List.replicate_add]
  simp

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
      rw [replicate_append_cons, List.replicate_succ, List.cons_append]
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

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

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
  have total := trace_trans _ (trace_trans _ (trace_trans _ (trace_trans _ first second)
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

end MinUncutGames.Foundations.Complexity.MachineInitialHeaders

end
section
namespace MinUncutGames.Foundations.PCP.RawInitialMachineModel

open Turing Complexity Hastad

inductive Tape
  | input | «variables» | counter | index | field (slot : Fin 6)
  | scratch | reversed | output
  deriving DecidableEq, Fintype

abbrev Signs := Bool × Bool × Bool
abbrev State := Signs × Option Bool
abbrev Alphabet (_ : Tape) := Bool

inductive CopyPhase
  | tailVariables (slot : Fin 3)
  | tailIndex (slot : Fin 3)
  | variableName (slot : Fin 3)
  | reverseIndex (slot : Fin 3) (orientation : Bool)
  | dummyVariables | dummyIndex | dummyReverse
  deriving DecidableEq, Fintype

inductive Label
  | headerStart (slot : Fin 2) | headerLoop (slot : Fin 2)
  | scanN | restoreN | scanM1 | restoreM1 | closeFirst
  | scanM6 | restoreM6 | closeSecond | initializeIndex | guard
  | fieldStart (slot : Fin 6) | fieldLoop (slot : Fin 6) | loadSigns
  | scan (phase : CopyPhase) | restore (phase : CopyPhase)
  | closeTail (slot : Fin 3) (orientation : Bool)
  | closeReverse (slot : Fin 3) (orientation : Bool)
  | relation (slot : Fin 3) (orientation : Bool)
  | cleanupField (slot : Fin 6) | incrementIndex
  | closeDummyTail | closeDummyReverse | dummyRelation
  | cleanupFinal (slot : Fin 3) | reset | finalReverse
  deriving DecidableEq, Fintype

def initialState : State := ((false, false, false), none)

def stateKeys : List State :=
  [false, true].flatMap fun a => [false, true].flatMap fun b =>
    [false, true].flatMap fun c =>
      [none, some false, some true].map fun register => ((a, b, c), register)

theorem stateKeys_complete (state : State) : state ∈ stateKeys := by
  rcases state with ⟨⟨a, b, c⟩, register⟩
  cases a <;> cases b <;> cases c <;> cases register with
  | none => simp [stateKeys]
  | some bit => cases bit <;> simp [stateKeys]

def nameField (slot : Fin 3) : Fin 6 := ⟨2 * slot.val, by omega⟩

def copySource : CopyPhase → Tape
  | .tailVariables _ | .dummyVariables => .«variables»
  | .variableName slot => .field (nameField slot)
  | _ => .index

def copyScale : CopyPhase → Nat
  | .reverseIndex _ _ | .dummyReverse => 6
  | _ => 1

def copyNext : CopyPhase → Label
  | .tailVariables slot => .scan (.tailIndex slot)
  | .tailIndex slot => .closeTail slot false
  | .variableName slot => .closeTail slot true
  | .reverseIndex slot orientation => .closeReverse slot orientation
  | .dummyVariables => .scan .dummyIndex
  | .dummyIndex => .closeDummyTail
  | .dummyReverse => .closeDummyReverse

def relationNext (slot : Fin 3) (orientation : Bool) : Label :=
  if orientation then
    if h : slot.val + 1 < 3 then .scan (.tailVariables ⟨slot.val + 1, h⟩)
    else .cleanupField 0
  else .scan (.variableName slot)

def finalTape (slot : Fin 3) : Tape :=
  if slot.val = 0 then .«variables» else if slot.val = 1 then .counter else .index

def drain (tape : Tape) (again next : Label) : TM2.Stmt Alphabet Label State :=
  MachineDrain.drain tape again (some next)

def headerTape (slot : Fin 2) : Tape := if slot.val = 0 then .«variables» else .counter

def relationOutput (slot : Fin 3) (orientation : Bool) (state : State) : List Bool :=
  (encodeWords (RawInitialRows.relationWordsFor state.1
    (RawInitialTables.slotOrder.symm slot) orientation)).reverse

def program : Label → TM2.Stmt Alphabet Label State
  | .headerStart slot => SourceMachine.fieldStart (headerTape slot) (.headerLoop slot)
  | .headerLoop slot => SourceMachine.fieldLoop .input (headerTape slot) (.headerLoop slot)
      (if slot.val = 0 then some (.headerStart 1) else some .scanN)
  | .scanN => MachineInitialHeaders.prefixScan .«variables» .scratch .reversed 1 .scanN .restoreN
  | .restoreN => Reduction.MachineTransfer.loopAt .scratch .«variables» id false .restoreN (some .scanM1)
  | .scanM1 => MachineInitialHeaders.prefixScan .counter .scratch .reversed 1 .scanM1 .restoreM1
  | .restoreM1 => Reduction.MachineTransfer.loopAt .scratch .counter id false .restoreM1 (some .closeFirst)
  | .closeFirst => Reduction.MachineSubstitution.pushWord .reversed [true, false]
      (.goto fun _ => .scanM6)
  | .scanM6 => MachineInitialHeaders.prefixScan .counter .scratch .reversed 6 .scanM6 .restoreM6
  | .restoreM6 => Reduction.MachineTransfer.loopAt .scratch .counter id false .restoreM6 (some .closeSecond)
  | .closeSecond => Reduction.MachineSubstitution.pushWord .reversed [true, false]
      (.goto fun _ => .initializeIndex)
  | .initializeIndex => .push .index (fun _ => false) (.goto fun _ => .guard)
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) (.scan .dummyVariables)
  | .fieldStart slot => SourceMachine.fieldStart (.field slot) (.fieldLoop slot)
  | .fieldLoop slot => SourceMachine.fieldLoop .input (.field slot) (.fieldLoop slot)
      (if h : slot.val + 1 < 6 then some (.fieldStart ⟨slot.val + 1, h⟩)
        else some .loadSigns)
  | .loadSigns =>
      .peek (.field 1) (fun state head => ((head.getD false, state.1.2), state.2))
        (.peek (.field 3) (fun state head => ((state.1.1, head.getD false, state.1.2.2), state.2))
          (.peek (.field 5) (fun state head => ((state.1.1, state.1.2.1, head.getD false), state.2))
            (.load (fun state => (state.1, none)) (.goto fun _ => .scan (.tailVariables 0)))))
  | .scan phase => MachineInitialHeaders.prefixScan (copySource phase) .scratch .reversed
      (copyScale phase) (.scan phase) (.restore phase)
  | .restore phase => Reduction.MachineTransfer.loopAt .scratch (copySource phase) id false
      (.restore phase) (some (copyNext phase))
  | .closeTail slot orientation => .push .reversed (fun _ => false)
      (.goto fun _ => .scan (.reverseIndex slot orientation))
  | .closeReverse slot orientation => Reduction.MachineSubstitution.pushWord .reversed
      (encodeWord (2 * slot.val + if orientation then 0 else 1))
        (.goto fun _ => .relation slot orientation)
  | .relation slot orientation => MachineFiniteTable.emit .reversed
      (relationOutput slot orientation)
      stateKeys (.goto fun _ => relationNext slot orientation)
  | .cleanupField slot => drain (.field slot) (.cleanupField slot)
      (if h : slot.val + 1 < 6 then .cleanupField ⟨slot.val + 1, h⟩ else .incrementIndex)
  | .incrementIndex => .push .index (fun _ => true) (.goto fun _ => .guard)
  | .closeDummyTail => .push .reversed (fun _ => false) (.goto fun _ => .scan .dummyReverse)
  | .closeDummyReverse => .push .reversed (fun _ => false) (.goto fun _ => .dummyRelation)
  | .dummyRelation => Reduction.MachineSubstitution.pushWord .reversed
      (encodeWords (GraphTables.relationWords (GraphTables.relationOf (fun _ _ => true))))
        (.goto fun _ => .cleanupFinal 0)
  | .cleanupFinal slot => drain (finalTape slot) (.cleanupFinal slot)
      (if h : slot.val + 1 < 3 then .cleanupFinal ⟨slot.val + 1, h⟩ else .reset)
  | .reset => .load (fun _ => initialState) (.goto fun _ => .finalReverse)
  | .finalReverse => Reduction.MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program

end MinUncutGames.Foundations.PCP.RawInitialMachineModel

end
section
namespace MinUncutGames.Foundations.PCP.RawInitialMachineStart

open Turing Complexity Hastad RawInitialMachineModel

def inputTapes (bits : List Bool) : Tape → List Bool
  | .input => bits
  | _ => []

private def firstTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => encodeWord m ++ clauseBits
  | .«variables» => encodeWord n
  | _ => []

def counterTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .«variables» => encodeWord n
  | .counter => encodeWord m
  | _ => []

private def headerTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .«variables» => encodeWord n
  | .counter => encodeWord m
  | .reversed => (encodeWords [n + m + 1, 6 * m + 1]).reverse
  | _ => []

def startTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .«variables» => encodeWord n
  | .counter => encodeWord m
  | .index => [false]
  | .reversed => (encodeWords [n + m + 1, 6 * m + 1]).reverse
  | _ => []

theorem initList_eq (bits : List Bool) :
    initList machine bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1
  funext k
  change Tape at k
  cases k <;> rfl

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]


theorem readCountersTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[n + m + 4]
      (some (initList machine (encodeWords [n, m] ++ clauseBits))) =
      some ⟨some .scanN, initialState, counterTapes n m clauseBits⟩ := by
  let t0 := inputTapes (encodeWords [n, m] ++ clauseBits)
  have first := (SourceMachine.fieldInTime .input .«variables» (by decide)
    (.headerStart 0) (.headerLoop 0) (some (.headerStart 1)) program rfl rfl
    t0 n (encodeWord m ++ clauseBits)
    (by simp [t0, inputTapes, encodeWords, List.append_assoc])
    (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[n + 2]
    (some ⟨some (.headerStart 0), initialState, t0⟩) = _ at first
  have firstFrame : SourceMachine.fieldTapes .input .«variables» t0
      (encodeWord m ++ clauseBits) (encodeWord n ++ t0 .«variables») =
      firstTapes n m clauseBits := by
    funext k
    cases k <;> simp [SourceMachine.fieldTapes, t0, inputTapes, firstTapes]
  rw [firstFrame] at first
  have second := (SourceMachine.fieldInTime .input .counter (by decide)
    (.headerStart 1) (.headerLoop 1) (some .scanN) program rfl rfl
    (firstTapes n m clauseBits) m clauseBits rfl (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[m + 2]
    (some ⟨some (.headerStart 1), initialState, firstTapes n m clauseBits⟩) = _ at second
  have secondFrame : SourceMachine.fieldTapes .input .counter (firstTapes n m clauseBits)
      clauseBits (encodeWord m ++ firstTapes n m clauseBits .counter) =
      counterTapes n m clauseBits := by
    funext k
    cases k <;> simp [SourceMachine.fieldTapes, firstTapes, counterTapes]
  rw [secondFrame] at second
  have total := trace_trans _ first second
  rw [show (n + 2) + (m + 2) = n + m + 4 by omega] at total
  simpa only [initList_eq, t0, initialState] using! total

theorem headersTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 4 * m + 8]
      (some ⟨some .scanN, initialState, counterTapes n m clauseBits⟩) =
      some ⟨some .initializeIndex, initialState, headerTapes n m clauseBits⟩ := by
  have h := MachineInitialHeaders.headerTrace .«variables» .counter .scratch .reversed
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    .scanN .restoreN .scanM1 .restoreM1 .closeFirst .scanM6 .restoreM6 .closeSecond
    (some .initializeIndex) program rfl rfl rfl rfl rfl rfl rfl rfl
    (counterTapes n m clauseBits) n m [] []
    (by simp [counterTapes]) (by simp [counterTapes]) rfl
    (false, false, false) none
  have frame : Function.update (counterTapes n m clauseBits) .reversed
      ((encodeWords [n + m + 1, 6 * m + 1]).reverse ++
        counterTapes n m clauseBits .reversed) = headerTapes n m clauseBits := by
    funext k
    cases k <;> simp [counterTapes, headerTapes]
  rw [frame] at h
  exact h

theorem initializeIndexTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .initializeIndex, initialState, headerTapes n m clauseBits⟩) =
      some ⟨some .guard, initialState, startTapes n m clauseBits⟩ := by
  simp only [Function.iterate_one, MachineComposition.advance_some]
  change some (TM2.stepAux (program .initializeIndex) initialState
    (headerTapes n m clauseBits)) = _
  simp only [program, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp [headerTapes, startTapes]

theorem startTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[3 * n + 5 * m + 13]
      (some (initList machine (encodeWords [n, m] ++ clauseBits))) =
      some ⟨some .guard, initialState, startTapes n m clauseBits⟩ := by
  have total := trace_trans _
    (trace_trans _ (readCountersTrace n m clauseBits) (headersTrace n m clauseBits))
    (initializeIndexTrace n m clauseBits)
  simpa only [show (n + m + 4) + (2 * n + 4 * m + 8) + 1 =
    3 * n + 5 * m + 13 by omega] using total

theorem formulaStartTrace (F : Target.Formula) :
    (MachineComposition.advance (TM2.step program))^[
        3 * F.«variables» + 5 * F.clauses.length + 13]
      (some (initList machine (formulaBits F))) =
      some ⟨some .guard, initialState,
        startTapes F.«variables» F.clauses.length
          (encodeWords (F.clauses.flatMap clauseWords))⟩ := by
  simpa only [formulaBits, formulaWords, encodeWords_append] using
    startTrace F.«variables» F.clauses.length (encodeWords (F.clauses.flatMap clauseWords))

def startInTime (n m : ℕ) (clauseBits : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (initList machine (encodeWords [n, m] ++ clauseBits))
      (some ⟨some .guard, initialState, startTapes n m clauseBits⟩)
      (3 * n + 5 * m + 13) where
  steps := 3 * n + 5 * m + 13
  evals_in_steps := startTrace n m clauseBits
  steps_le_m := Nat.le_refl _

def formulaStartInTime (F : Target.Formula) :
    StateTransition.EvalsToInTime (TM2.step program) (initList machine (formulaBits F))
      (some ⟨some .guard, initialState,
        startTapes F.«variables» F.clauses.length
          (encodeWords (F.clauses.flatMap clauseWords))⟩)
      (3 * F.«variables» + 5 * F.clauses.length + 13) where
  steps := 3 * F.«variables» + 5 * F.clauses.length + 13
  evals_in_steps := formulaStartTrace F
  steps_le_m := Nat.le_refl _

end MinUncutGames.Foundations.PCP.RawInitialMachineStart

end
section
namespace MinUncutGames.Foundations.PCP.RawInitialMachineLoopData

open Target Complexity RawInitialMachineModel

def clauseInput {n : Nat} (clauses : List (Clause n)) : List Bool :=
  encodeWords (clauses.flatMap Complexity.clauseWords)

@[simp] theorem clauseInput_nil (n : Nat) : clauseInput ([] : List (Clause n)) = [] := rfl

@[simp] theorem clauseInput_cons {n : Nat} (c : Clause n) (cs : List (Clause n)) :
    clauseInput (c :: cs) = encodeWords (Complexity.clauseWords c) ++ clauseInput cs := by
  simp only [clauseInput, List.flatMap_cons, encodeWords_append]

def clauseOutput (n i : Nat) (clauses : List (Clause n)) : List Nat :=
  (clauses.mapIdx fun offset c => RawInitialRows.clauseWords n (i + offset)
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c)).flatten

private theorem mapIdx_ofFn {α β : Type} (xs : List α) (f : Nat → α → β) :
    xs.mapIdx f = List.ofFn (fun i : Fin xs.length => f i.val (xs.get i)) := by
  induction xs generalizing f with
  | nil => simp
  | cons x xs ih => simp [ih]

@[simp] theorem clauseOutput_nil (n i : Nat) : clauseOutput n i [] = [] := rfl

@[simp] theorem clauseOutput_cons (n i : Nat) (c : Clause n) (cs : List (Clause n)) :
    clauseOutput n i (c :: cs) =
      RawInitialRows.clauseWords n i (RawInitialRows.clauseNames c)
        (RawInitialRows.clauseSigns c) ++ clauseOutput n (i + 1) cs := by
  simp only [clauseOutput, List.mapIdx_cons, Nat.add_zero, List.flatten_cons,
    Nat.add_comm, Nat.add_left_comm]

theorem clauseOutput_numbered (F : Formula) :
    clauseOutput F.«variables» 0 F.clauses =
      (List.finRange F.clauses.length).flatMap (fun i =>
        RawInitialRows.clauseWords F.«variables» i.val
          (RawInitialRows.clauseNames (clauseAt F i))
          (RawInitialRows.clauseSigns (clauseAt F i))) := by
  simp only [clauseOutput, mapIdx_ofFn, List.ofFn_eq_map,
    Nat.zero_add, clauseAt]
  rfl

theorem tableWords_decomposition (F : Formula) :
    GraphTables.tableWords (RawInitialTables.table F) =
      [F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
        clauseOutput F.«variables» 0 F.clauses ++
          RawInitialRows.dummyWords F.«variables» F.clauses.length := by
  rw [RawInitialRows.tableWords_eq, clauseOutput_numbered]

def loopTapes (n i remaining : Nat) (input reversed : List Bool) : Tape → List Bool
  | .input => input
  | .«variables» => encodeWord n
  | .counter => encodeWord remaining
  | .index => encodeWord i
  | .reversed => reversed
  | _ => []

theorem startTapes_eq (n m : Nat) (input : List Bool) :
    RawInitialMachineStart.startTapes n m input =
      loopTapes n 0 m input (encodeWords [n + m + 1, 6 * m + 1]).reverse := by
  funext tape
  cases tape <;> rfl

theorem decrement_counter (n i remaining : Nat) (input reversed : List Bool) :
    Function.update (loopTapes n i (remaining + 1) input reversed)
      Tape.counter (encodeWord remaining) = loopTapes n i remaining input reversed := by
  funext tape
  cases tape <;> simp [loopTapes]

theorem increment_index (n i remaining : Nat) (input reversed : List Bool) :
    Function.update (loopTapes n i remaining input reversed)
      Tape.index (true :: encodeWord i) = loopTapes n (i + 1) remaining input reversed := by
  funext tape
  cases tape <;> simp [loopTapes, encodeWord, List.replicate_succ]

end MinUncutGames.Foundations.PCP.RawInitialMachineLoopData

end

end OAI
