import OAI.Computability.BinPacking.Arithmetic.GraphTallyMachine
import OAI.Computability.BinPacking.Computation.MachineCanonicalOutput
import OAI.Computability.BinPacking.CookLevin.VerifierCircuit

namespace OAI

namespace BinPackingGap.PairFirstProjection

open Turing BinPackingGames.Foundations.Complexity MachineComposition

inductive Tape
  | input | counter | reversed | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .counter, .reversed, .output]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | scan | copy | reverse
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .copy, .reverse]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State := Option Bool

def tapes (input counter reversed output : List Bool) : Tape → List Bool
  | .input => input
  | .counter => counter
  | .reversed => reversed
  | .output => output

@[simp] theorem tapes_input (a b c d : List Bool) : tapes a b c d .input = a := rfl
@[simp] theorem tapes_counter (a b c d : List Bool) : tapes a b c d .counter = b := rfl
@[simp] theorem tapes_reversed (a b c d : List Bool) : tapes a b c d .reversed = c := rfl
@[simp] theorem tapes_output (a b c d : List Bool) : tapes a b c d .output = d := rfl

@[simp] theorem update_input (a b c d e : List Bool) :
    Function.update (tapes a b c d) .input e = tapes e b c d := by
  funext k
  cases k <;> rfl

@[simp] theorem update_counter (a b c d e : List Bool) :
    Function.update (tapes a b c d) .counter e = tapes a e c d := by
  funext k
  cases k <;> rfl

@[simp] theorem update_reversed (a b c d e : List Bool) :
    Function.update (tapes a b c d) .reversed e = tapes a b e d := by
  funext k
  cases k <;> rfl

@[simp] theorem update_output (a b c d e : List Bool) :
    Function.update (tapes a b c d) .output e = tapes a b c e := by
  funext k
  cases k <;> rfl

def code : Label → TM2.Stmt (fun _ : Tape => Bool) Label State
  | .scan => .pop .input (fun _ head => head)
      (.branch (fun head => head.getD false)
        (.push .counter (fun _ => true) (.goto fun _ => .scan))
        (.goto fun _ => .copy))
  | .copy => .pop .counter (fun _ head => head)
      (.branch Option.isSome
        (.pop .input (fun _ head => head)
          (.push .reversed (fun head => head.getD false) (.goto fun _ => .copy)))
        (.goto fun _ => .reverse))
  | .reverse => .pop .reversed (fun _ head => head)
      (.branch Option.isSome
        (.push .output (fun head => head.getD false) (.goto fun _ => .reverse))
        .halt)

def program : MachineCanonicalOutput.Program Tape Label State where
  input := .input
  output := .output
  main := .scan
  initial := none
  code := code

abbrev machine := MachineCanonicalOutput.sourceMachine program

def cfg (label : Option Label) (state : State)
    (input counter reversed output : List Bool) : machine.Cfg :=
  ⟨label, state, tapes input counter reversed output⟩

theorem scan_true (r : State) (a b c d : List Bool) :
    machine.step (cfg (some .scan) r (true :: a) b c d) =
      some (cfg (some .scan) (some true) a (true :: b) c d) := by
  simp [FinTM2.step, TM2.step, machine, MachineCanonicalOutput.sourceMachine,
    program, code, cfg, TM2.stepAux]
  apply congrArg (fun stk => some (⟨some .scan, some true, stk⟩ : machine.Cfg))
  funext k
  cases k <;> rfl

theorem scan_false (r : State) (a b c d : List Bool) :
    machine.step (cfg (some .scan) r (false :: a) b c d) =
      some (cfg (some .copy) (some false) a b c d) := by
  simp [FinTM2.step, TM2.step, machine, MachineCanonicalOutput.sourceMachine,
    program, code, cfg, TM2.stepAux]
  apply congrArg (fun stk => some (⟨some .copy, some false, stk⟩ : machine.Cfg))
  funext k
  cases k <;> rfl

theorem copy_cons (r : State) (bit : Bool) (a b c d : List Bool) :
    machine.step (cfg (some .copy) r (bit :: a) (true :: b) c d) =
      some (cfg (some .copy) (some bit) a b (bit :: c) d) := by
  simp [FinTM2.step, TM2.step, machine, MachineCanonicalOutput.sourceMachine,
    program, code, cfg, TM2.stepAux]
  apply congrArg (fun stk => some (⟨some .copy, some bit, stk⟩ : machine.Cfg))
  funext k
  cases k <;> rfl

theorem copy_nil (r : State) (a c d : List Bool) :
    machine.step (cfg (some .copy) r a [] c d) =
      some (cfg (some .reverse) none a [] c d) := by
  simp [FinTM2.step, TM2.step, machine, MachineCanonicalOutput.sourceMachine,
    program, code, cfg, TM2.stepAux]
  apply congrArg (fun stk => some (⟨some .reverse, none, stk⟩ : machine.Cfg))
  funext k
  cases k <;> rfl

theorem reverse_cons (r : State) (bit : Bool) (a b c d : List Bool) :
    machine.step (cfg (some .reverse) r a b (bit :: c) d) =
      some (cfg (some .reverse) (some bit) a b c (bit :: d)) := by
  simp [FinTM2.step, TM2.step, machine, MachineCanonicalOutput.sourceMachine,
    program, code, cfg, TM2.stepAux]
  apply congrArg (fun stk => some (⟨some .reverse, some bit, stk⟩ : machine.Cfg))
  funext k
  cases k <;> rfl

theorem reverse_nil (r : State) (a b d : List Bool) :
    machine.step (cfg (some .reverse) r a b [] d) =
      some (cfg none none a b [] d) := by
  simp [FinTM2.step, TM2.step, machine, MachineCanonicalOutput.sourceMachine,
    program, code, cfg, TM2.stepAux]
  apply congrArg (fun stk => some (⟨none, none, stk⟩ : machine.Cfg))
  funext k
  cases k <;> rfl

theorem scan_trace (n m : Nat) (r : State) (rest c d : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some .scan) r (encodeWord n ++ rest)
        (List.replicate m true) c d)) =
    some (cfg (some .copy) (some false) rest
      (List.replicate (m + n) true) c d) := by
  induction n generalizing m r with
  | zero =>
      simpa [encodeWord, advance, Option.bind_some] using!
        scan_false r rest (List.replicate m true) c d
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp only [encodeWord, List.replicate_succ, List.cons_append, advance_some,
        scan_true]
      have h := ih (m + 1) (some true)
      simpa [encodeWord, List.replicate_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h

theorem copy_trace (word rest acc out : List Bool) (r : State) :
    (advance machine.step)^[word.length + 1]
      (some (cfg (some .copy) r (word ++ rest)
        (List.replicate word.length true) acc out)) =
    some (cfg (some .reverse) none rest [] (word.reverse ++ acc) out) := by
  induction word generalizing acc r with
  | nil => simpa [advance, Option.bind_some] using! copy_nil r rest acc out
  | cons bit word ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [List.cons_append, List.replicate_succ, advance_some, copy_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: acc) (some bit)

theorem reverse_trace (word rest counter out : List Bool) (r : State) :
    (advance machine.step)^[word.length + 1]
      (some (cfg (some .reverse) r rest counter word out)) =
    some (cfg none none rest counter [] (word.reverse ++ out)) := by
  induction word generalizing out r with
  | nil => simpa [advance, Option.bind_some] using! reverse_nil r rest counter out
  | cons bit word ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some, reverse_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: out) (some bit)

theorem init_eq (input : List Bool) :
    initList machine input = cfg (some .scan) none input [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  cases k <;> rfl

theorem projection_trace (x witness : List Bool) :
    (advance machine.step)^[3 * x.length + 3]
      (some (initList machine (CookLevin.pairBits (x, witness)))) =
    some (cfg none none witness [] [] x) := by
  have hs := scan_trace x.length 0 none (x ++ witness) [] []
  have hc := copy_trace x witness [] [] (some false)
  have hr := reverse_trace x.reverse witness [] [] none
  simp only [Nat.zero_add, List.replicate_zero] at hs
  simp only [List.append_nil] at hc
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  rw [init_eq]
  have hn : 3 * x.length + 3 = (x.length + 1) + ((x.length + 1) + (x.length + 1)) := by omega
  rw [hn]
  simpa only [CookLevin.pairBits, List.append_assoc, Function.iterate_add_apply] using
    (show (advance machine.step)^[x.length + 1]
      ((advance machine.step)^[x.length + 1]
        ((advance machine.step)^[x.length + 1]
          (some (cfg (some .scan) none (encodeWord x.length ++ (x ++ witness)) [] [] [])))) =
        some (cfg none none witness [] [] x) from by rw [hs, hc, hr])

noncomputable def rawTime : Polynomial Nat := 3 * Polynomial.X + 3

def rawRun (p : List Bool × List Bool) :
    MachineCanonicalOutput.TerminalRun program (CookLevin.pairBits p) p.1
      (rawTime.eval (CookLevin.pairBits p).length) where
  state := none
  tapes := tapes p.2 [] [] p.1
  execution := {
    steps := 3 * p.1.length + 3
    evals_in_steps := projection_trace p.1 p.2
    steps_le_m := by
      simp [rawTime, CookLevin.pairBits_length]
      omega }
  output_eq := rfl

def cleanupTapes : List Tape := [.input, .counter, .reversed]

theorem cleanup_complete (k : Tape) : k ∈ cleanupTapes ↔ k ≠ program.output := by
  cases k <;> simp [cleanupTapes, program]

noncomputable def computation :
    TM2ComputableInPolyTime CookLevin.pairBits (id : List Bool → List Bool)
      (fun p : List Bool × List Bool => p.1) :=
  MachineCanonicalOutput.computableInPolyTime program cleanupTapes cleanup_complete
    CookLevin.pairBits id (fun p => p.1) rawTime rawRun

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet program cleanupTapes
    cleanup_complete CookLevin.pairBits id (fun p => p.1) rawTime rawRun

end BinPackingGap.PairFirstProjection

namespace BinPackingGap

open Turing BinPackingGames.Foundations.Complexity

theorem inP_to_inNP {L : BitLanguage} (hL : InP L) : CookLevin.InNP L := by
  classical
  obtain ⟨decider, computation, finiteAlphabet, correct⟩ := hL
  let combined := MachineSequential.composeBits PairFirstProjection.computation computation
  have combinedFinite : MachineFiniteAlphabet.FiniteAlphabet combined.tm :=
    MachineFiniteAlphabet.composeBits PairFirstProjection.computation computation
      PairFirstProjection.finiteAlphabet finiteAlphabet
  let verifier : CookLevin.NPVerifier := {
    witnessBound := 0
    verify := fun p => decider p.1
    computation := combined
    finiteAlphabet := fun k => by
      letI : Finite (combined.tm.Γ k) := combinedFinite k
      exact Fintype.ofFinite (combined.tm.Γ k) }
  refine ⟨verifier, ?_⟩
  intro x
  change L x ↔ ∃ witness : List Bool,
    witness.length ≤ (0 : Polynomial Nat).eval x.length ∧ decider x = true
  constructor
  · intro hx
    exact ⟨[], by simp, (correct x).mp hx⟩
  · rintro ⟨_, _, accepted⟩
    exact (correct x).mpr accepted

theorem classP_subset_classNP : ClassP ⊆ ClassNP :=
  fun _ h => inP_to_inNP h

theorem pEqualsNP_iff_np_subset_p :
    PEqualsNP ↔ ∀ L : BitLanguage, CookLevin.InNP L → InP L := by
  constructor
  · intro equal L hL
    change L ∈ ClassP
    rw [equal]
    exact hL
  · intro inclusion
    apply Set.Subset.antisymm classP_subset_classNP
    exact fun L hL => inclusion L hL

theorem PEqualsNP.inP (h : PEqualsNP) {L : BitLanguage}
    (hL : CookLevin.InNP L) : InP L :=
  pEqualsNP_iff_np_subset_p.mp h L hL

structure PromiseProblem (α : Type) where
  yes : α → Prop
  no : α → Prop
  disjoint : ∀ y, ¬ (yes y ∧ no y)

structure PolynomialPromiseReduction (L : BitLanguage) {α : Type}
    (encode : α → List Bool) (P : PromiseProblem α) where
  reduce : List Bool → α
  computation : TM2ComputableInPolyTime (id : List Bool → List Bool) encode reduce
  finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm
  completeness : ∀ x, L x → P.yes (reduce x)
  soundness : ∀ x, ¬L x → P.no (reduce x)

def PromiseNPHard {α : Type} (encode : α → List Bool)
    (P : PromiseProblem α) : Prop :=
  ∀ L : BitLanguage, CookLevin.InNP L →
    Nonempty (PolynomialPromiseReduction L encode P)

structure PolynomialPromiseDecider {α : Type} (encode : α → List Bool)
    (P : PromiseProblem α) where
  decide : α → Bool
  computation : TM2ComputableInPolyTime encode (fun b => [b]) decide
  finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm
  yes_correct : ∀ y, P.yes y → decide y = true
  no_correct : ∀ y, P.no y → decide y = false

theorem PolynomialPromiseReduction.inP {α : Type} {L : BitLanguage}
    {encode : α → List Bool} {P : PromiseProblem α}
    (reduction : PolynomialPromiseReduction L encode P)
    (decider : PolynomialPromiseDecider encode P) : InP L := by
  refine ⟨fun x => decider.decide (reduction.reduce x),
    MachineSequential.composeBits reduction.computation decider.computation,
    MachineFiniteAlphabet.composeBits reduction.computation decider.computation
      reduction.finiteAlphabet decider.finiteAlphabet, ?_⟩
  intro x
  constructor
  · intro hx
    exact decider.yes_correct _ (reduction.completeness x hx)
  · intro accepted
    change decider.decide (reduction.reduce x) = true at accepted
    by_contra rejected
    have hfalse := decider.no_correct _ (reduction.soundness x rejected)
    rw [accepted] at hfalse
    cases hfalse

theorem PromiseNPHard.pEqualsNP {α : Type} {encode : α → List Bool}
    {P : PromiseProblem α} (hard : PromiseNPHard encode P)
    (decider : PolynomialPromiseDecider encode P) : PEqualsNP := by
  apply pEqualsNP_iff_np_subset_p.mpr
  intro L hL
  obtain ⟨reduction⟩ := hard L hL
  exact reduction.inP decider

def packingPromise (c : Nat) : PromiseProblem RawReductionOutput where
  yes out := ∃ hr : out.2.Valid, HasPacking (out.2.toInstance hr) out.1
  no out := ∃ hr : out.2.Valid, ¬HasPacking (out.2.toInstance hr) (out.1 + c)
  disjoint out := by
    rintro ⟨⟨hr, yes⟩, ⟨_, no⟩⟩
    exact no (yes.mono (Nat.le_add_right out.1 c))

def PackingGapReduction.toPromiseReduction {c : Nat} {L : BitLanguage}
    (reduction : PackingGapReduction c L) :
    PolynomialPromiseReduction L BinaryEncoding.rawReductionOutputBits
      (packingPromise c) where
  reduce := reduction.reduce
  computation := reduction.computation
  finiteAlphabet := reduction.finiteAlphabet
  completeness x hx := ⟨reduction.valid x, reduction.completeness x hx⟩
  soundness x hx := ⟨reduction.valid x, reduction.soundness x hx⟩

theorem PackingGapNPHard.promiseNPHard {c : Nat} (hard : PackingGapNPHard c) :
    PromiseNPHard BinaryEncoding.rawReductionOutputBits (packingPromise c) := by
  intro L hL
  obtain ⟨reduction⟩ := hard L hL
  exact ⟨reduction.toPromiseReduction⟩

end BinPackingGap

end OAI
