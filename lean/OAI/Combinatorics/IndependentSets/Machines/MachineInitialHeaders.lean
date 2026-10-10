import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineTransfer
import OAI.Combinatorics.IndependentSets.Machines.MachineCopy
import OAI.Combinatorics.IndependentSets.Machines.PushWord

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineInitialHeaders

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

private theorem update_source (source scratch output : K)
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

private theorem update_output (source scratch output : K)
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

end IndependentSetsGames.Foundations.Complexity.MachineInitialHeaders

end OAI
