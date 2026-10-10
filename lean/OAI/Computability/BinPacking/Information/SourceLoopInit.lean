import OAI.Computability.BinPacking.Computation.PoweringMasterState

namespace OAI

namespace BinPackingGames.Foundations.Hastad.SourceClauseLookup

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition SourceMachine

section Discard

variable {K Λ σ : Type} [DecidableEq K]

theorem discardFieldsTrace (source : K) (label : Nat → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (atLoop : ∀ r, r < values.length → program (label (offset + r)) =
      MachineLookup.discard source (label (offset + r)) (label (offset + r + 1)))
    (hinput : base source = encodeWords values ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords values).length]
      (some ⟨some (label offset), (ambient, none), base⟩) =
      some ⟨some (label (offset + values.length)), (ambient, none),
        Function.update base source suffix⟩ := by
  induction values generalizing base offset with
  | nil =>
    have hbase : Function.update base source suffix = base := by
      have hs : base source = suffix := by simpa only [encodeWords, List.nil_append] using hinput
      funext p
      by_cases hp : p = source
      · subst p; simp [hs]
      · simp [hp]
    simp only [encodeWords, List.length_nil, Nat.add_zero, Function.iterate_zero_apply, hbase]
  | cons n rest ih =>
    have hs : program (label offset) =
        MachineLookup.discard source (label offset) (label (offset + 1)) := by
      simpa only [Nat.add_zero] using atLoop 0 (by simp)
    have hin : base source = encodeWord n ++ (encodeWords rest ++ suffix) := by
      simpa only [encodeWords, List.append_assoc] using hinput
    have first := MachineLookup.discardTrace source (label offset) (label (offset + 1))
      program hs base n (encodeWords rest ++ suffix) hin ambient none
    have htail : ∀ r, r < rest.length → program (label (offset + 1 + r)) =
        MachineLookup.discard source (label (offset + 1 + r))
          (label (offset + 1 + r + 1)) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        atLoop (r + 1) (by simp; omega)
    have second := ih (Function.update base source (encodeWords rest ++ suffix))
      (offset + 1) htail (by simp)
    rw [show (encodeWords (n :: rest)).length = (encodeWords rest).length + (n + 1) by
      simp only [encodeWords, List.length_append, encodeWord_length]
      omega]
    rw [Function.iterate_add_apply, first]
    simpa [Function.update_idem, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

end Discard

inductive Tape
  | formula | index | work | scratch | field (slot : Fin 6)
  deriving DecidableEq, Fintype

inductive Label
  | copyOut | copyBack | headerFirst | headerSecond | guard
  | skip (slot : Fin 6)
  | read (slot : Fin 7 × Bool)
  deriving DecidableEq, Fintype

def fieldDestination (r : Nat) : Tape := .field ⟨min r 5, by omega⟩
def readStart (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 6 r, false)
def readLoop (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 6 r, true)
def skipLabel (r : Nat) : Label := if h : r < 6 then .skip ⟨r, h⟩ else .guard
def headerLabel (r : Nat) : Label :=
  if r = 0 then .headerFirst else if r = 1 then .headerSecond else .guard

def program : Label → TM2.Stmt (fun _ : Tape => Bool) Label (Unit × Option Bool)
  | .copyOut => Reduction.MachineTransfer.loopAt .formula .scratch id false
      .copyOut (some .copyBack)
  | .copyBack => MachineCopy.forkLoop .scratch .formula .work false
      .copyBack (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .guard
  | .guard => MachineUnaryCounter.guard .index (skipLabel 0) (readStart 0)
  | .skip slot => MachineLookup.discard .work (.skip slot) (skipLabel (slot.val + 1))
  | .read slot =>
      if slot.1.val < 6 then
        if slot.2 then
          fieldLoop .work (fieldDestination slot.1.val) (.read (slot.1, true))
            (some (readStart (slot.1.val + 1)))
        else fieldStart (fieldDestination slot.1.val) (.read (slot.1, true))
      else SourceFieldArray.finish .work none

def machine : FinTM2 where
  K := Tape
  k₀ := .formula
  k₁ := .field 0
  Γ _ := Bool
  Λ := Label
  main := .copyOut
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program

theorem atSkip (r : Nat) (hr : r < 6) :
    program (skipLabel r) = MachineLookup.discard .work (skipLabel r) (skipLabel (r + 1)) := by
  simp [skipLabel, hr, program]

theorem atReadStart (r : Nat) (hr : r < 6) :
    program (readStart r) = fieldStart (fieldDestination r) (readLoop r) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadLoop (r : Nat) (hr : r < 6) :
    program (readLoop r) = fieldLoop .work (fieldDestination r) (readLoop r)
      (some (readStart (r + 1))) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadDone : program (readStart 6) = SourceFieldArray.finish .work none := by
  simp [program, readStart, SourceFieldArray.boundedIndex]

theorem discardHeadersTrace (base : Tape → List Bool) (variableCount clauses : Nat)
    (suffix : List Bool) (hinput : base .work = encodeWords [variableCount, clauses] ++ suffix) :
    (advance (TM2.step program))^[variableCount + clauses + 2]
      (some ⟨some .headerFirst, ((), none), base⟩) =
      some ⟨some .guard, ((), none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work headerLabel program base 0 [variableCount, clauses]
    suffix (by
      intro r hr
      have he : r = 0 ∨ r = 1 := by simp at hr; omega
      rcases he with rfl | rfl <;> rfl) hinput ()
  simpa [encodeWords_length, headerLabel] using ht

theorem discardSixTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 6) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    (advance (TM2.step program))^[(encodeWords values).length]
      (some ⟨some (skipLabel 0), ((), none), base⟩) =
      some ⟨some .guard, ((), none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work skipLabel program base 0 values suffix
    (by intro r hr; simpa only [Nat.zero_add] using atSkip r (by omega)) hinput ()
  simpa [hlen, skipLabel] using ht

theorem readSixTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 6) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    (advance (TM2.step program))^[(encodeWords values).length + 7]
      (some ⟨some (readStart 0), ((), none), base⟩) =
      some ⟨none, ((), none),
        SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix⟩ := by
  have ht := SourceFieldArray.sequenceTrace .work fieldDestination readStart readLoop none
    program base 0 values suffix (by intro r hr; simp [fieldDestination])
    (by intro r hr; simpa only [Nat.zero_add] using atReadStart r (by omega))
    (by intro r hr; simpa only [Nat.zero_add] using atReadLoop r (by omega))
    (by simpa [hlen] using atReadDone) hinput () none
  have htime : values.sum + 2 * values.length + 1 = (encodeWords values).length + 7 := by
    rw [encodeWords_length, hlen]
  simpa only [Nat.zero_add, htime] using ht

def scanTapes (base : Tape → List Bool) (index : Nat)
    (indexSuffix input : List Bool) : Tape → List Bool :=
  MachineUnaryCounter.counterTapes .index (Function.update base .work input) index indexSuffix

@[simp] theorem scanTapes_work (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) : scanTapes base i indexSuffix input .work = input := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

@[simp] theorem scanTapes_index (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) :
    scanTapes base i indexSuffix input .index = encodeWord i ++ indexSuffix := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

theorem scanTapes_other (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) (p : Tape) (hi : p ≠ .index) (hw : p ≠ .work) :
    scanTapes base i indexSuffix input p = base p := by
  simp [scanTapes, MachineUnaryCounter.counterTapes, hi, hw]

theorem update_scanTapes_work (base : Tape → List Bool) (i : Nat)
    (indexSuffix input replacement : List Bool) :
    Function.update (scanTapes base i indexSuffix input) .work replacement =
      scanTapes base i indexSuffix replacement := by
  funext p
  cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes]

theorem skipClausesTrace {n : Nat} (base : Tape → List Bool)
    (prior : List (Target.Clause n)) (indexSuffix suffix : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords (prior.flatMap clauseWords)).length + prior.length + 1]
      (some ⟨some .guard, ((), register), scanTapes base prior.length indexSuffix
        (encodeWords (prior.flatMap clauseWords) ++ suffix)⟩) =
      some ⟨some (readStart 0), ((), none), scanTapes base 0 indexSuffix suffix⟩ := by
  induction prior generalizing register with
  | nil =>
    simpa only [List.flatMap_nil, List.length_nil, encodeWords, List.nil_append,
      Nat.zero_add, Function.iterate_one, advance_some, scanTapes] using
      MachineUnaryCounter.guardStep_zero .index .guard (skipLabel 0) (readStart 0)
        program rfl (Function.update base .work suffix) indexSuffix () register
  | cons clause prior ih =>
    have hencoding : encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix =
        encodeWords (clauseWords clause) ++ (encodeWords (prior.flatMap clauseWords) ++ suffix) := by
      simp only [List.flatMap_cons, encodeWords_append, List.append_assoc]
    have htime : (encodeWords ((clause :: prior).flatMap clauseWords)).length +
        (clause :: prior).length + 1 =
        ((encodeWords (prior.flatMap clauseWords)).length + prior.length + 1 +
          (encodeWords (clauseWords clause)).length) + 1 := by
      simp only [List.flatMap_cons, encodeWords_append, List.length_append, List.length_cons]
      omega
    rw [htime, Function.iterate_succ_apply]
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap clauseWords)).length + prior.length + 1 +
        (encodeWords (clauseWords clause)).length]
      (TM2.step program ⟨some .guard, ((), register),
        MachineUnaryCounter.counterTapes .index
          (Function.update base .work (encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix))
          (prior.length + 1) indexSuffix⟩) = _
    rw [MachineUnaryCounter.guardStep_succ .index .guard (skipLabel 0) (readStart 0)
      program rfl]
    rw [Function.iterate_add_apply]
    have hd := discardSixTrace
      (scanTapes base prior.length indexSuffix
        (encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix))
      (clauseWords clause) (clauseWords_length clause)
      (encodeWords (prior.flatMap clauseWords) ++ suffix) (by
        rw [scanTapes_work, hencoding])
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap clauseWords)).length + prior.length + 1]
      ((advance (TM2.step program))^[(encodeWords (clauseWords clause)).length]
        (some ⟨some (skipLabel 0), ((), none), scanTapes base prior.length indexSuffix
          (encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix)⟩)) = _
    rw [hd, update_scanTapes_work]
    exact ih none

theorem fieldDestination_eq (j : Fin 6) : fieldDestination j.val = .field j := by
  unfold fieldDestination
  congr 1
  apply Fin.ext
  exact Nat.min_eq_left (by omega)

theorem fieldDestination_injective_below (r s : Nat) (hr : r < 6) (hs : s < 6)
    (he : fieldDestination r = fieldDestination s) : r = s := by
  have hv := congrArg (fun t : Tape => match t with | .field j => j.val | _ => 6) he
  simpa [fieldDestination, Nat.min_eq_left (show r ≤ 5 by omega),
    Nat.min_eq_left (show s ≤ 5 by omega)] using hv

theorem readSix_output_field (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 6) (suffix : List Bool) (j : Fin 6) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix (.field j) =
      encodeWord (values[j.val]'(by omega)) ++ base (.field j) := by
  have ht := SourceFieldArray.sequenceTapes_selected .work fieldDestination base 0 values
    suffix j.val (by omega) (by intro r hr; simp [fieldDestination])
    (by
      intro r s hr hs he
      apply fieldDestination_injective_below r s (by omega) (by omega)
      simpa only [Nat.zero_add] using he)
  simpa only [Nat.zero_add, fieldDestination_eq] using ht

theorem readSix_output_work (base : Tape → List Bool) (values : List Nat)
    (_hlen : values.length = 6) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix .work = suffix := by
  apply SourceFieldArray.sequenceTapes_source _ _ _ _ _ _ _ hinput
  intro r hr
  simp [fieldDestination]

theorem readSix_output_frame (base : Tape → List Bool) (values : List Nat)
    (suffix : List Bool) (p : Tape) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 6, p ≠ .field j) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix p = base p := by
  apply SourceFieldArray.sequenceTapes_other _ _ _ hwork
  intro r hr
  exact hfield _

def outputTapes {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) : Tape → List Bool :=
  SourceFieldArray.sequenceTapes .work fieldDestination
    (scanTapes base 0 indexSuffix (encodeWords (clauseWords clause) ++ suffix))
    0 (clauseWords clause) suffix

def scanSteps {n : Nat} (variableCount declaredClauses : Nat)
    (prior : List (Target.Clause n)) (clause : Target.Clause n) : Nat :=
  variableCount + declaredClauses + 2 +
    (encodeWords (prior.flatMap clauseWords)).length + prior.length + 1 +
    (encodeWords (clauseWords clause)).length + 7

theorem scanReadTrace {n : Nat} (base : Tape → List Bool) (variableCount declaredClauses : Nat)
    (prior : List (Target.Clause n)) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) :
    (advance (TM2.step program))^[scanSteps variableCount declaredClauses prior clause]
      (some ⟨some .headerFirst, ((), none), scanTapes base prior.length indexSuffix
        (encodeWords [variableCount, declaredClauses] ++
          (encodeWords (prior.flatMap clauseWords) ++
            (encodeWords (clauseWords clause) ++ suffix)))⟩) =
      some ⟨none, ((), none), outputTapes base clause indexSuffix suffix⟩ := by
  have hh := discardHeadersTrace
    (scanTapes base prior.length indexSuffix
      (encodeWords [variableCount, declaredClauses] ++
        (encodeWords (prior.flatMap clauseWords) ++ (encodeWords (clauseWords clause) ++ suffix))))
    variableCount declaredClauses
    (encodeWords (prior.flatMap clauseWords) ++ (encodeWords (clauseWords clause) ++ suffix))
    (by simp)
  have hs := skipClausesTrace base prior indexSuffix (encodeWords (clauseWords clause) ++ suffix) none
  have hr := readSixTrace
    (scanTapes base 0 indexSuffix (encodeWords (clauseWords clause) ++ suffix))
    (clauseWords clause) (clauseWords_length clause) suffix (by simp)
  rw [show scanSteps variableCount declaredClauses prior clause =
      ((encodeWords (clauseWords clause)).length + 7 +
        ((encodeWords (prior.flatMap clauseWords)).length + prior.length + 1)) +
        (variableCount + declaredClauses + 2) by unfold scanSteps; omega]
  rw [Function.iterate_add_apply, hh, update_scanTapes_work,
    Function.iterate_add_apply, hs]
  exact hr

def lookupSteps {n : Nat} (F : Target.Formula) (prior : List (Target.Clause n))
    (clause : Target.Clause n) : Nat :=
  2 * ((formulaBits F).length + 1) + scanSteps F.variables F.clauses.length prior clause

theorem lookupWithSplitTrace (F : Target.Formula) (prior : List (Target.Clause F.variables))
    (clause : Target.Clause F.variables) (after : List (Target.Clause F.variables))
    (hsplit : F.clauses = prior ++ clause :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    (advance (TM2.step program))^[lookupSteps F prior clause]
      (some ⟨some .copyOut, ((), register), base⟩) =
      some ⟨none, ((), none),
        outputTapes base clause indexSuffix (encodeWords (after.flatMap clauseWords))⟩ := by
  have hbits : formulaBits F = encodeWords [F.variables, F.clauses.length] ++
      (encodeWords (prior.flatMap clauseWords) ++
        (encodeWords (clauseWords clause) ++ encodeWords (after.flatMap clauseWords))) := by
    simp only [formulaBits, formulaWords, encodeWords_append]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append]
  have hc := MachineCopy.copyTrace .formula .work .scratch (by decide) (by decide)
    (by decide) false .copyOut .copyBack (some .headerFirst) program rfl rfl
    base hscratch () register
  have htapes : Function.update base .work (base .formula ++ base .work) =
      scanTapes base prior.length indexSuffix (formulaBits F) := by
    funext p
    cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes, hformula, hindex, hwork]
  rw [htapes, hformula] at hc
  rw [lookupSteps, Nat.add_comm, Function.iterate_add_apply, hc, hbits]
  exact scanReadTrace base F.variables F.clauses.length prior clause indexSuffix
    (encodeWords (after.flatMap clauseWords))

theorem output_formula {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) :
    outputTapes base clause indexSuffix suffix .formula = base .formula := by
  rw [outputTapes, readSix_output_frame _ _ _ .formula (by decide) (by intro j; simp)]
  exact scanTapes_other _ _ _ _ _ (by decide) (by decide)

theorem output_index {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) :
    outputTapes base clause indexSuffix suffix .index = encodeWord 0 ++ indexSuffix := by
  rw [outputTapes, readSix_output_frame _ _ _ .index (by decide) (by intro j; simp),
    scanTapes_index]

theorem output_work {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) :
    outputTapes base clause indexSuffix suffix .work = suffix := by
  apply readSix_output_work _ _ (clauseWords_length clause) _
  simp

theorem output_field {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) (j : Fin 6) :
    outputTapes base clause indexSuffix suffix (.field j) =
      encodeWord ((clauseWords clause)[j.val]'(by simp)) ++ base (.field j) := by
  rw [outputTapes, readSix_output_field _ _ (clauseWords_length clause)]
  rw [scanTapes_other _ _ _ _ (.field j) (by simp) (by simp)]

theorem output_frame {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) (p : Tape) (hindex : p ≠ .index) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 6, p ≠ .field j) :
    outputTapes base clause indexSuffix suffix p = base p := by
  rw [outputTapes, readSix_output_frame _ _ _ p hwork hfield]
  exact scanTapes_other _ _ _ _ p hindex hwork

theorem clauseWords_six {n : Nat} (clause : Target.Clause n) :
    clauseWords clause =
      [clause[0].variableIndex.val, if clause[0].positive then 1 else 0,
       clause[1].variableIndex.val, if clause[1].positive then 1 else 0,
       clause[2].variableIndex.val, if clause[2].positive then 1 else 0] := rfl

def fieldWords (tapes : Tape → List Bool) : List (List Bool) :=
  [tapes (.field 0), tapes (.field 1), tapes (.field 2),
   tapes (.field 3), tapes (.field 4), tapes (.field 5)]

theorem output_fieldWords {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) (hempty : ∀ j : Fin 6, base (.field j) = []) :
    fieldWords (outputTapes base clause indexSuffix suffix) =
      (clauseWords clause).map encodeWord := by
  simp [fieldWords, output_field, hempty, clauseWords_six]

theorem lookupSteps_le_input (F : Target.Formula) (prior : List (Target.Clause F.variables))
    (clause : Target.Clause F.variables) (after : List (Target.Clause F.variables))
    (hsplit : F.clauses = prior ++ clause :: after) :
    lookupSteps F prior clause ≤ 4 * (formulaBits F).length + 10 := by
  have hlength : (formulaBits F).length = F.variables + F.clauses.length + 2 +
      (encodeWords (prior.flatMap clauseWords)).length +
      (encodeWords (clauseWords clause)).length +
      (encodeWords (after.flatMap clauseWords)).length := by
    simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
      encodeWords, encodeWord_length, List.length_nil]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append, List.length_append]
    omega
  have hp : prior.length ≤ F.clauses.length := by
    rw [hsplit, List.length_append, List.length_cons]
    omega
  unfold lookupSteps scanSteps
  omega

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 10

theorem timePolynomial_eval (L : Nat) : timePolynomial.eval L = 4 * L + 10 := by
  simp [timePolynomial]

def lookupWithSplitInTime (F : Target.Formula) (prior : List (Target.Clause F.variables))
    (clause : Target.Clause F.variables) (after : List (Target.Clause F.variables))
    (hsplit : F.clauses = prior ++ clause :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, ((), register), base⟩
      (some ⟨none, ((), none),
        outputTapes base clause indexSuffix (encodeWords (after.flatMap clauseWords))⟩)
      (timePolynomial.eval (formulaBits F).length) where
  steps := lookupSteps F prior clause
  evals_in_steps := lookupWithSplitTrace F prior clause after hsplit base indexSuffix
    hformula hindex hwork hscratch register
  steps_le_m := by
    rw [timePolynomial_eval]
    exact lookupSteps_le_input F prior clause after hsplit

def lookupInTime (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord i.val ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, ((), register), base⟩
      (some ⟨none, ((), none), outputTapes base F.clauses[i.val] indexSuffix
        (encodeWords ((F.clauses.drop (i.val + 1)).flatMap clauseWords))⟩)
      (timePolynomial.eval (formulaBits F).length) := by
  have hp : (F.clauses.take i.val).length = i.val := by
    rw [List.length_take, Nat.min_eq_left i.isLt.le]
  have hs : F.clauses = F.clauses.take i.val ++ F.clauses[i.val] :: F.clauses.drop (i.val + 1) := by
    rw [List.getElem_cons_drop i.isLt, List.take_append_drop]
  apply lookupWithSplitInTime F (F.clauses.take i.val) F.clauses[i.val]
    (F.clauses.drop (i.val + 1)) hs base indexSuffix hformula
    (by simpa only [hp] using hindex) hwork hscratch register

def machineInTime (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord i.val ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some .copyOut, ((), register), base⟩
      (some ⟨none, ((), none), outputTapes base F.clauses[i.val] indexSuffix
        (encodeWords ((F.clauses.drop (i.val + 1)).flatMap clauseWords))⟩)
      (timePolynomial.eval (formulaBits F).length) := by
  exact lookupInTime F i base indexSuffix hformula hindex hwork hscratch register

end BinPackingGames.Foundations.Hastad.SourceClauseLookup

namespace BinPackingGames.Foundations.Hastad.SourceContextLoad

open Turing BinPackingGames.Foundations.Complexity
open MachineComposition

inductive Tape (u : Nat) (Extra : Type)
  | formula | index | work | scratch | copyScratch
  | current (coordinate : Fin u) | remaining (coordinate : Fin u)
  | field (coordinate : Fin u) (slot : Fin 6)
  | extra (value : Extra)
  deriving DecidableEq, Fintype

inductive Label (u : Nat)
  | copyOut (coordinate : Fin u) | copyBack (coordinate : Fin u)
  | lookup (coordinate : Fin u) (localLabel : SourceClauseLookup.Label)
  | clearWork (coordinate : Fin u) | clearIndex (coordinate : Fin u)
  | done
  deriving DecidableEq, Fintype

variable {u : Nat} {Extra : Type}

def place (j : Fin u) : SourceClauseLookup.Tape → Tape u Extra
  | .formula => .formula | .index => .index | .work => .work | .scratch => .scratch
  | .field s => .field j s

def fill (j : Fin u) (base : Tape u Extra → List Bool)
    (localTapes : SourceClauseLookup.Tape → List Bool) : Tape u Extra → List Bool
  | .formula => localTapes .formula | .index => localTapes .index
  | .work => localTapes .work | .scratch => localTapes .scratch
  | .field i s => if i = j then localTapes (.field s) else base (.field i s)
  | p => base p

@[simp] theorem fill_place (j : Fin u) (base : Tape u Extra → List Bool)
    (localTapes : SourceClauseLookup.Tape → List Bool) (p : SourceClauseLookup.Tape) :
    fill j base localTapes (place j p) = localTapes p := by
  cases p <;> simp [fill, place]

@[simp] theorem fill_self (j : Fin u) (base : Tape u Extra → List Bool) :
    fill j base (base ∘ place j) = base := by
  funext p
  cases p <;> simp [fill, place]
  intro h
  subst h
  rfl

variable [DecidableEq Extra]

theorem fill_update (j : Fin u) (base : Tape u Extra → List Bool)
    (localTapes : SourceClauseLookup.Tape → List Bool) (p : SourceClauseLookup.Tape)
    (value : List Bool) :
    fill j base (Function.update localTapes p value) =
      Function.update (fill j base localTapes) (place j p) value := by
  funext k
  cases k <;> cases p <;> simp [fill, place, Function.update_apply]
  all_goals split <;> simp_all

def placedLabel (j : Fin u) : Option SourceClauseLookup.Label → Option (Label u)
  | none => some (.clearWork j)
  | some l => some (.lookup j l)

def placedConfiguration (j : Fin u) (base : Tape u Extra → List Bool)
    (c : TM2.Cfg (fun _ : SourceClauseLookup.Tape => Bool)
      SourceClauseLookup.Label (Unit × Option Bool)) :
    TM2.Cfg (fun _ : Tape u Extra => Bool) (Label u) (Unit × Option Bool) :=
  ⟨placedLabel j c.l, c.var, fill j base c.stk⟩

def placedStatement (j : Fin u) :
    TM2.Stmt (fun _ : SourceClauseLookup.Tape => Bool)
      SourceClauseLookup.Label (Unit × Option Bool) →
    TM2.Stmt (fun _ : Tape u Extra => Bool) (Label u) (Unit × Option Bool)
  | .push k f next => .push (place j k) f (placedStatement j next)
  | .peek k f next => .peek (place j k) f (placedStatement j next)
  | .pop k f next => .pop (place j k) f (placedStatement j next)
  | .load f next => .load f (placedStatement j next)
  | .branch f yes no => .branch f (placedStatement j yes) (placedStatement j no)
  | .goto f => .goto (fun state => .lookup j (f state))
  | .halt => .goto (fun _ => .clearWork j)

theorem placed_stepAux (j : Fin u) (base : Tape u Extra → List Bool)
    (q : TM2.Stmt (fun _ : SourceClauseLookup.Tape => Bool)
      SourceClauseLookup.Label (Unit × Option Bool))
    (state : Unit × Option Bool) (localTapes : SourceClauseLookup.Tape → List Bool) :
    TM2.stepAux (placedStatement j q) state (fill j base localTapes) =
      placedConfiguration j base (TM2.stepAux q state localTapes) := by
  induction q generalizing state localTapes with
  | push k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih state _
  | peek k f next ih =>
    simpa only [placedStatement, TM2.stepAux, fill_place] using ih (f state _) localTapes
  | pop k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih (f state _) _
  | load f next ih => simpa only [placedStatement, TM2.stepAux] using ih (f state) localTapes
  | branch f yes no ihYes ihNo =>
    cases h : f state
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state localTapes
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state localTapes
  | goto f => rfl
  | halt => rfl

def nextLabel (j : Fin u) : Label u :=
  if h : j.val + 1 < u then .copyOut ⟨j.val + 1, h⟩ else .done

def program : Label u → TM2.Stmt (fun _ : Tape u Extra => Bool)
    (Label u) (Unit × Option Bool)
  | .copyOut j => Reduction.MachineTransfer.loopAt (.current j) .copyScratch id false
      (.copyOut j) (some (.copyBack j))
  | .copyBack j => MachineCopy.forkLoop .copyScratch (.current j) .index false
      (.copyBack j) (some (.lookup j .copyOut))
  | .lookup j l => placedStatement j (SourceClauseLookup.program l)
  | .clearWork j => MachineDrain.drain .work (.clearWork j) (some (.clearIndex j))
  | .clearIndex j => MachineDrain.drain .index (.clearIndex j) (some (nextLabel j))
  | .done => .halt

theorem placed_step (j : Fin u) (base : Tape u Extra → List Bool)
    (a b : TM2.Cfg (fun _ : SourceClauseLookup.Tape => Bool)
      SourceClauseLookup.Label (Unit × Option Bool))
    (h : TM2.step SourceClauseLookup.program a = some b) :
    TM2.step program (placedConfiguration j base a) =
      some (placedConfiguration j base b) := by
  cases a with
  | mk l state localTapes =>
    cases l with
    | none => contradiction
    | some l =>
      change some (TM2.stepAux (SourceClauseLookup.program l) state localTapes) = some b at h
      cases Option.some.inj h
      change some (TM2.stepAux (placedStatement j (SourceClauseLookup.program l))
        state (fill j base localTapes)) = _
      rw [placed_stepAux]

def lookupOutput (j : Fin u) (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : List Bool) : Tape u Extra → List Bool :=
  fill j base (SourceClauseLookup.outputTapes (base ∘ place j) F.clauses[i.val] suffix
    (encodeWords ((F.clauses.drop (i.val + 1)).flatMap clauseWords)))

noncomputable def placedLookupInTime (j : Fin u) (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord i.val ++ suffix)
    (hwork : base .work = []) (hscratch : base .scratch = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.lookup j .copyOut), ((), register), base⟩
      (some ⟨some (.clearWork j), ((), none), lookupOutput j F i base suffix⟩)
      (4 * (formulaBits F).length + 10) := by
  have h := SourceClauseLookup.lookupInTime F i (base ∘ place j) suffix
    hformula hindex hwork hscratch register
  have lifted := liftExecutionInTime (TM2.step SourceClauseLookup.program) (TM2.step program)
    (placedConfiguration j base) (placed_step j base) h
  simpa only [placedConfiguration, placedLabel, fill_self,
    SourceClauseLookup.timePolynomial_eval, lookupOutput] using lifted

def copiedTapes (j : Fin u) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  Function.update base .index (base (.current j))

def coordinateOutput {n : Nat} (j : Fin u) (clause : Target.Clause n)
    (base : Tape u Extra → List Bool) : Tape u Extra → List Bool
  | .index | .work => []
  | .field k s => if k = j then
      encodeWord ((clauseWords clause)[s.val]'(by simp)) ++ base (.field k s)
    else base (.field k s)
  | p => base p

theorem cleanup_lookupOutput (j : Fin u) (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : List Bool) :
    Function.update (Function.update
      (lookupOutput j F i (copiedTapes j base) suffix) .work []) .index [] =
      coordinateOutput j F.clauses[i.val] base := by
  funext p
  cases p with
  | formula => simp [lookupOutput, fill, coordinateOutput, SourceClauseLookup.output_formula,
      copiedTapes, place]
  | index => simp [coordinateOutput]
  | work => simp [coordinateOutput]
  | scratch =>
    simp only [Function.update_of_ne (by simp : (Tape.scratch : Tape u Extra) ≠ .index),
      Function.update_of_ne (by simp : (Tape.scratch : Tape u Extra) ≠ .work), lookupOutput, fill,
      coordinateOutput]
    rw [SourceClauseLookup.output_frame _ _ _ _ .scratch (by simp) (by simp) (by intro s; simp)]
    simp [copiedTapes, place]
  | field k s =>
    by_cases hk : k = j
    · subst k
      simp [lookupOutput, fill, coordinateOutput, SourceClauseLookup.output_field,
        copiedTapes, place]
    · simp [lookupOutput, fill, coordinateOutput, hk, copiedTapes]
  | copyScratch => simp [lookupOutput, fill, coordinateOutput, copiedTapes]
  | current k => simp [lookupOutput, fill, coordinateOutput, copiedTapes]
  | remaining k => simp [lookupOutput, fill, coordinateOutput, copiedTapes]
  | extra k => simp [lookupOutput, fill, coordinateOutput, copiedTapes]

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_current {n : Nat} (j k : Fin u) (clause : Target.Clause n)
    (base : Tape u Extra → List Bool) :
    coordinateOutput j clause base (.current k) = base (.current k) := rfl

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_remaining {n : Nat} (j k : Fin u) (clause : Target.Clause n)
    (base : Tape u Extra → List Bool) :
    coordinateOutput j clause base (.remaining k) = base (.remaining k) := rfl

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_field {n : Nat} (j : Fin u) (s : Fin 6)
    (clause : Target.Clause n) (base : Tape u Extra → List Bool) :
    coordinateOutput j clause base (.field j s) =
      encodeWord ((clauseWords clause)[s.val]'(by simp)) ++ base (.field j s) := by
  simp [coordinateOutput]

omit [DecidableEq Extra] in
theorem coordinateOutput_other_field {n : Nat} (j k : Fin u) (s : Fin 6)
    (clause : Target.Clause n) (base : Tape u Extra → List Bool) (h : k ≠ j) :
    coordinateOutput j clause base (.field k s) = base (.field k s) := by
  simp [coordinateOutput, h]

theorem suffix_length_le_input (F : Target.Formula) (i : Nat) :
    (encodeWords ((F.clauses.drop i).flatMap clauseWords)).length ≤ (formulaBits F).length := by
  have hs := List.take_append_drop i F.clauses
  have he : formulaBits F = encodeWords [F.variables, F.clauses.length] ++
      encodeWords ((F.clauses.take i).flatMap clauseWords) ++
      encodeWords ((F.clauses.drop i).flatMap clauseWords) := by
    conv_lhs => rw [formulaBits, formulaWords, ← hs]
    simp only [List.flatMap_append, encodeWords_append, List.append_assoc]
    rw [hs]
  rw [he, List.length_append, List.length_append]
  omega

noncomputable def coordinateInTime (j : Fin u) (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : base (.current j) = encodeWord i.val ++ suffix)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.copyOut j), ((), register), base⟩
      (some ⟨some (nextLabel j), ((), none), coordinateOutput j F.clauses[i.val] base⟩)
      (6 * (formulaBits F).length + 4 * (base (.current j)).length + 20) := by
  let copied := copiedTapes j base
  let loaded := lookupOutput j F i copied suffix
  have copyRun := MachineCopy.copyInTime (.current j) .index .copyScratch
    (by simp) (by simp) (by simp) false (.copyOut j) (.copyBack j)
    (some (.lookup j .copyOut)) program rfl rfl base hcopy () register
  have copied_eq : Function.update base .index (base (.current j) ++ base .index) = copied := by
    simp [copied, copiedTapes, hindex]
  rw [copied_eq] at copyRun
  have lookupRun := placedLookupInTime j F i copied suffix
    (by simpa [copied, copiedTapes] using hformula)
    (by simpa [copied, copiedTapes] using hcurrent)
    (by simpa [copied, copiedTapes] using hwork)
    (by simpa [copied, copiedTapes] using hscratch) none
  have workRun := MachineDrain.drainInTime .work (.clearWork j) (some (.clearIndex j))
    program rfl loaded () none
  have indexRun := MachineDrain.drainInTime .index (.clearIndex j) (some (nextLabel j))
    program rfl (Function.update loaded .work []) () none
  have hrun := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copyRun lookupRun)
      workRun) indexRun
  have hw : loaded .work = encodeWords ((F.clauses.drop (i.val + 1)).flatMap clauseWords) := by
    simp [loaded, lookupOutput, fill, SourceClauseLookup.output_work]
  have hi : (Function.update loaded .work []) .index = encodeWord 0 ++ suffix := by
    simp [loaded, lookupOutput, fill, SourceClauseLookup.output_index]
  have hc : suffix.length ≤ (base (.current j)).length := by
    rw [hcurrent, List.length_append]
    omega
  refine { steps := hrun.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [loaded, copied, cleanup_lookupOutput] using hrun.evals_in_steps
  · apply Nat.le_trans hrun.steps_le_m
    rw [hw, hi, List.length_append, encodeWord_length]
    have hs := suffix_length_le_input F (i.val + 1)
    omega

def labelAt (r : Nat) : Label u :=
  if h : r < u then .copyOut ⟨r, h⟩ else .done

theorem nextLabel_eq (j : Fin u) : nextLabel j = labelAt (j.val + 1) := rfl

def stageTapes (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) : Nat → Tape u Extra → List Bool
  | 0 => base
  | r + 1 => if h : r < u then
      coordinateOutput ⟨r, h⟩ F.clauses[(tuple ⟨r, h⟩).val] (stageTapes F tuple base r)
    else stageTapes F tuple base r

omit [DecidableEq Extra] in
theorem stageTapes_frame (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (r : Nat) (p : Tape u Extra)
    (hi : p ≠ .index) (hw : p ≠ .work) (hf : ∀ j s, p ≠ .field j s) :
    stageTapes F tuple base r p = base p := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [stageTapes]
    split
    · cases p <;> simp_all [coordinateOutput]
    · exact ih

omit [DecidableEq Extra] in
theorem stageTapes_clean (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (r : Nat) (hi : base .index = []) (hw : base .work = []) :
    stageTapes F tuple base r .index = [] ∧ stageTapes F tuple base r .work = [] := by
  induction r with
  | zero => exact ⟨hi, hw⟩
  | succ r ih =>
    simp only [stageTapes]
    split
    · exact ⟨rfl, rfl⟩
    · exact ih

omit [DecidableEq Extra] in
theorem stageTapes_field (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (r : Nat) (j : Fin u) (s : Fin 6) :
    stageTapes F tuple base r (.field j s) = if j.val < r then
      encodeWord ((clauseWords F.clauses[(tuple j).val])[s.val]'(by simp)) ++ base (.field j s)
      else base (.field j s) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r, hr⟩ : Fin u)
      · subst j
        simp only [coordinateOutput_field, ih]
        simp
      · rw [coordinateOutput_other_field _ _ _ _ _ hj, ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r + 1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r + 1 := by omega
      simp only [hjr, hjr', ite_true]

noncomputable def prefixInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : Fin u → List Bool) (C : Nat)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.current j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (r : Nat) (hr : r ≤ u) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨some (labelAt r), ((), none), stageTapes F tuple base r⟩)
      (r * (6 * (formulaBits F).length + 4 * C + 20)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hru : r < u := by omega
    let j : Fin u := ⟨r, hru⟩
    let before := stageTapes F tuple base r
    have hf (p : Tape u Extra) (hi : p ≠ .index) (hw : p ≠ .work)
        (hh : ∀ j s, p ≠ .field j s) : before p = base p :=
      stageTapes_frame F tuple base r p hi hw hh
    have hd := stageTapes_clean F tuple base r hindex hwork
    have hc : before (.current j) = base (.current j) := hf _ (by simp) (by simp) (by simp)
    have one := coordinateInTime j F (tuple j) before (suffix j)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hformula)
      (by rw [hc]; exact hcurrent j) hd.1 hd.2
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hscratch)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hcopy) none
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt r), ((), none), before⟩
        (some ⟨some (labelAt (r + 1)), ((), none), stageTapes F tuple base (r + 1)⟩)
        (6 * (formulaBits F).length + 4 * C + 20) := by
      refine { steps := one.steps, evals_in_steps := ?_, steps_le_m := ?_ }
      · simpa only [labelAt, dite_eq_left hru, nextLabel_eq, j, stageTapes, before] using
          one.evals_in_steps
      · apply Nat.le_trans one.steps_le_m
        rw [hc]
        have hs := hsize j
        omega
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (ih (by omega)) one'
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using joined

noncomputable def loadInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : Fin u → List Bool) (C : Nat)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.current j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨none, ((), none), stageTapes F tuple base u⟩)
      (u * (6 * (formulaBits F).length + 4 * C + 20) + 1) := by
  have prefixRun := prefixInTime F tuple base suffix C hformula hcurrent hsize
    hindex hwork hscratch hcopy u (Nat.le_refl _)
  have doneRun : StateTransition.EvalsToInTime (TM2.step (program (Extra := Extra)))
      ⟨some (labelAt u), ((), none), stageTapes F tuple base u⟩
      (some ⟨none, ((), none), stageTapes F tuple base u⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (labelAt u), ((), none), stageTapes F tuple base u⟩ = _
    simp only [labelAt, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ prefixRun doneRun

theorem clauses_length_le_input (F : Target.Formula) :
    F.clauses.length ≤ (formulaBits F).length := by
  simp only [formulaBits, encodeWords_length, formulaWords_length]
  omega

noncomputable def loadUnaryInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨none, ((), none), stageTapes F tuple base u⟩)
      (u * (10 * (formulaBits F).length + 20) + 1) := by
  have run := loadInTime F tuple base (fun _ => []) (formulaBits F).length hformula
    (by simpa only [List.append_nil] using hcurrent)
    (by
      intro j
      rw [hcurrent j, encodeWord_length]
      have h := (tuple j).isLt
      have hm := clauses_length_le_input F
      omega)
    hindex hwork hscratch hcopy
  have he : 6 * (formulaBits F).length + 4 * (formulaBits F).length + 20 =
      10 * (formulaBits F).length + 20 := by omega
  simpa only [he] using run

noncomputable def timePolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C (10 * u) * Polynomial.X + Polynomial.C (20 * u + 1)

theorem timePolynomial_eval (u L : Nat) :
    (timePolynomial u).eval L = u * (10 * L + 20) + 1 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]

def variableSlot (s : Fin 3) : Fin 6 := ⟨2 * s.val, by omega⟩
def polaritySlot (s : Fin 3) : Fin 6 := ⟨2 * s.val + 1, by omega⟩
def variableField (j : Fin u) (s : Fin 3) : Tape u Extra := .field j (variableSlot s)
def polarityField (j : Fin u) (s : Fin 3) : Tape u Extra := .field j (polaritySlot s)

theorem clauseWords_variable {n : Nat} (clause : Target.Clause n) (s : Fin 3) :
    (clauseWords clause)[(variableSlot s).val]'(by simp) = clause[s.val].variableIndex.val := by
  obtain ⟨s, hs⟩ := s
  have h : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases h with rfl | rfl | rfl <;> rfl

theorem clauseWords_polarity {n : Nat} (clause : Target.Clause n) (s : Fin 3) :
    (clauseWords clause)[(polaritySlot s).val]'(by simp) =
      if clause[s.val].positive then 1 else 0 := by
  obtain ⟨s, hs⟩ := s
  have h : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases h with rfl | rfl | rfl <;> rfl

omit [DecidableEq Extra] in
theorem output_variable (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (j : Fin u) (s : Fin 3) :
    stageTapes F tuple base u (variableField j s) =
      encodeWord (F.clauses[(tuple j).val][s.val].variableIndex.val) ++ base (variableField j s) := by
  rw [variableField, stageTapes_field, ite_eq_left j.isLt, clauseWords_variable]

omit [DecidableEq Extra] in
theorem output_polarity (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (j : Fin u) (s : Fin 3) :
    stageTapes F tuple base u (polarityField j s) =
      encodeWord (if F.clauses[(tuple j).val][s.val].positive then 1 else 0) ++
        base (polarityField j s) := by
  rw [polarityField, stageTapes_field, ite_eq_left j.isLt, clauseWords_polarity]

variable [Fintype Extra]

def machine (u : Nat) (Extra : Type) [DecidableEq Extra] [Fintype Extra] : FinTM2 where
  K := Tape u Extra
  k₀ := .formula
  k₁ := .formula
  Γ _ := Bool
  Λ := Label u
  main := labelAt 0
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program

end BinPackingGames.Foundations.Hastad.SourceContextLoad

namespace BinPackingGames.Foundations.Hastad.SourceLoopInit

open Turing BinPackingGames.Foundations.Complexity
open MachineComposition SourceMachine

inductive HeaderTape
  | variableCount | clauseCount
  deriving DecidableEq

protected abbrev HeaderTape.enumList : List HeaderTape := [.variableCount, .clauseCount]

protected theorem HeaderTape.enumList_getElem?_ctorIdx_eq (x : HeaderTape) :
    HeaderTape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem HeaderTape.enumList_nodup : HeaderTape.enumList.Nodup := by decide

instance : Fintype HeaderTape where
  elems := ⟨HeaderTape.enumList, HeaderTape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape (u : Nat) (Extra : Type) := SourceContextLoad.Tape u (HeaderTape ⊕ Extra)

inductive Label (u : Nat)
  | inputCopyOut | inputCopyBack | read (slot : Fin 3 × Bool) | clearWork
  | seed (j : Fin u) | digitCopyOut (j : Fin u) | digitCopyBack (j : Fin u)
  | trim (j : Fin u) | done
  deriving DecidableEq, Fintype

variable {u : Nat} {Extra : Type}

def variableHeader : Tape u Extra := .extra (.inl .variableCount)
def clauseHeader : Tape u Extra := .extra (.inl .clauseCount)
def headerDestination (r : Nat) : Tape u Extra := if r = 0 then variableHeader else clauseHeader
def readStart (r : Nat) : Label u := .read (SourceFieldArray.boundedIndex 2 r, false)
def readLoop (r : Nat) : Label u := .read (SourceFieldArray.boundedIndex 2 r, true)
def labelAt (r : Nat) : Label u := if h : r < u then .seed ⟨r, h⟩ else .done

def program : Label u → TM2.Stmt (fun _ : Tape u Extra => Bool) (Label u) (Unit × Option Bool)
  | .inputCopyOut => Reduction.MachineTransfer.loopAt .formula .scratch id false
      .inputCopyOut (some .inputCopyBack)
  | .inputCopyBack => MachineCopy.forkLoop .scratch .formula .work false
      .inputCopyBack (some (readStart 0))
  | .read slot => if slot.1.val < 2 then
      if slot.2 then fieldLoop .work (headerDestination slot.1.val) (.read (slot.1, true))
        (some (readStart (slot.1.val + 1)))
      else fieldStart (headerDestination slot.1.val) (.read (slot.1, true))
    else SourceFieldArray.finish .work (some .clearWork)
  | .clearWork => MachineDrain.drain .work .clearWork (some (labelAt 0))
  | .seed j => .push (.current j) (fun _ => false) (.goto fun _ => .digitCopyOut j)
  | .digitCopyOut j => Reduction.MachineTransfer.loopAt clauseHeader .copyScratch id false
      (.digitCopyOut j) (some (.digitCopyBack j))
  | .digitCopyBack j => MachineCopy.forkLoop .copyScratch clauseHeader (.remaining j) false
      (.digitCopyBack j) (some (.trim j))
  | .trim j => .pop (.remaining j) (fun state _ => state) (.goto fun _ => labelAt (j.val + 1))
  | .done => .halt

theorem atReadStart (r : Nat) (hr : r < 2) :
    program (u := u) (Extra := Extra) (readStart r) =
      fieldStart (headerDestination r) (readLoop r) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadLoop (r : Nat) (hr : r < 2) :
    program (u := u) (Extra := Extra) (readLoop r) = fieldLoop .work (headerDestination r)
      (readLoop r) (some (readStart (r + 1))) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadDone : program (u := u) (Extra := Extra) (readStart 2) =
    SourceFieldArray.finish .work (some .clearWork) := by
  simp [program, readStart]

variable [DecidableEq Extra]

def copiedInput (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  Function.update base .work (base .formula)

def readOutput (F : Target.Formula) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  SourceFieldArray.sequenceTapes .work headerDestination (copiedInput base) 0
    [F.variables, F.clauses.length] (encodeWords (F.clauses.flatMap clauseWords))

def headerOutput (F : Target.Formula) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  Function.update (Function.update (Function.update base .work []) variableHeader
    (encodeWord F.variables ++ base variableHeader)) clauseHeader
    (encodeWord F.clauses.length ++ base clauseHeader)

theorem clear_readOutput (F : Target.Formula) (base : Tape u Extra → List Bool) :
    Function.update (readOutput F base) .work [] = headerOutput F base := by
  funext p
  cases p <;> simp [readOutput, headerOutput, SourceFieldArray.sequenceTapes,
    afterField, fieldTapes, copiedInput, headerDestination, variableHeader, clauseHeader]
  rename_i e
  cases e with
  | inl h => cases h <;> simp
  | inr e => simp

theorem readOutput_work (F : Target.Formula) (base : Tape u Extra → List Bool) :
    readOutput F base .work = encodeWords (F.clauses.flatMap clauseWords) := by
  simp [readOutput, SourceFieldArray.sequenceTapes, afterField, fieldTapes,
    headerDestination, variableHeader, clauseHeader, encodeWords]

theorem headerOutput_frame (F : Target.Formula) (base : Tape u Extra → List Bool)
    (p : Tape u Extra) (hw : p ≠ .work) (hn : p ≠ variableHeader) (hm : p ≠ clauseHeader) :
    headerOutput F base p = base p := by simp [headerOutput, hw, hn, hm]

def headerInTime (F : Target.Formula) (base : Tape u Extra → List Bool)
    (hformula : base .formula = formulaBits F) (hwork : base .work = [])
    (hscratch : base .scratch = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .inputCopyOut, ((), register), base⟩
      (some ⟨some (labelAt 0), ((), none), headerOutput F base⟩)
      (3 * (formulaBits F).length + 6) := by
  have copying := MachineCopy.copyInTime .formula .work .scratch
    (by simp) (by simp) (by simp) false .inputCopyOut .inputCopyBack (some (readStart 0))
    program rfl rfl base hscratch () register
  have hc : Function.update base .work (base .formula ++ base .work) = copiedInput base := by
    simp [copiedInput, hwork]
  rw [hc] at copying
  have reading := SourceFieldArray.sequenceInTime .work headerDestination readStart readLoop
    (some .clearWork) program (copiedInput base) 0 [F.variables, F.clauses.length]
    (encodeWords (F.clauses.flatMap clauseWords))
    (by intro r hr; simp [headerDestination, variableHeader, clauseHeader]; split <;> simp)
    (by intro r hr; simpa only [Nat.zero_add] using atReadStart (u := u) (Extra := Extra) r (by simpa using hr))
    (by intro r hr; simpa only [Nat.zero_add] using atReadLoop (u := u) (Extra := Extra) r (by simpa using hr))
    (by simpa using (atReadDone (u := u) (Extra := Extra)))
    (by simp [copiedInput, hformula, formulaBits, formulaWords, encodeWords, List.append_assoc]) () none
  have draining := MachineDrain.drainInTime .work .clearWork (some (labelAt 0))
    program rfl (readOutput F base) () none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copying reading) draining
  refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [clear_readOutput] using joined.evals_in_steps
  · apply Nat.le_trans joined.steps_le_m
    rw [readOutput_work, hformula]
    have he : (formulaBits F).length = F.variables + F.clauses.length + 2 +
        (encodeWords (F.clauses.flatMap clauseWords)).length := by
      simp [formulaBits, formulaWords, encodeWords, Nat.add_assoc]
      omega
    simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
    omega

def digitOutput (j : Fin u) (m : Nat) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  Function.update (Function.update base (.current j) (encodeWord 0)) (.remaining j) (encodeWord (m - 1))

theorem digitOutput_frame (j : Fin u) (m : Nat) (base : Tape u Extra → List Bool)
    (p : Tape u Extra) (hc : p ≠ .current j) (hr : p ≠ .remaining j) :
    digitOutput j m base p = base p := by simp [digitOutput, hc, hr]

def digitInTime (j : Fin u) (m : Nat) (hm : 0 < m) (base : Tape u Extra → List Bool)
    (hcount : base clauseHeader = encodeWord m)
    (hcurrent : base (.current j) = []) (hremaining : base (.remaining j) = [])
    (hscratch : base .copyScratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.seed j), ((), none), base⟩
      (some ⟨some (labelAt (j.val + 1)), ((), none), digitOutput j m base⟩)
      (2 * m + 6) := by
  let seeded := Function.update base (.current j) (encodeWord 0)
  have seedRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.seed j), ((), none), base⟩
      (some ⟨some (.digitCopyOut j), ((), none), seeded⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (.seed j), ((), none), base⟩ = _
    simp [program, TM2.step, TM2.stepAux, seeded, hcurrent, encodeWord]
  have copying := MachineCopy.copyInTime clauseHeader (.remaining j) .copyScratch
    (by simp [clauseHeader]) (by simp [clauseHeader]) (by simp)
    false (.digitCopyOut j) (.digitCopyBack j) (some (.trim j)) program rfl rfl seeded
    (by simpa [seeded] using hscratch) () none
  let copied := Function.update seeded (.remaining j) (encodeWord m)
  have he : Function.update seeded (.remaining j)
      (seeded clauseHeader ++ seeded (.remaining j)) = copied := by
    have hcount' : base (.extra (.inl .clauseCount)) = encodeWord m := hcount
    simp [copied, seeded, clauseHeader, hremaining, hcount']
  rw [he] at copying
  have trimRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.trim j), ((), none), copied⟩
      (some ⟨some (labelAt (j.val + 1)), ((), none), digitOutput j m base⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (.trim j), ((), none), copied⟩ = _
    have hn : m = (m - 1) + 1 := by omega
    have htail : (encodeWord m).tail = encodeWord (m - 1) := by
      conv_lhs => rw [hn]
      simp [encodeWord, List.replicate_succ]
    simp [program, TM2.step, TM2.stepAux, copied, seeded, digitOutput, htail]
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ seedRun copying) trimRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  have hs : seeded clauseHeader = encodeWord m := by simpa [seeded, clauseHeader] using hcount
  rw [hs, encodeWord_length]
  omega

def stageTapes (m : Nat) (base : Tape u Extra → List Bool) : Nat → Tape u Extra → List Bool
  | 0 => base
  | r + 1 => if h : r < u then digitOutput ⟨r, h⟩ m (stageTapes m base r)
    else stageTapes m base r

theorem stageTapes_frame (m : Nat) (base : Tape u Extra → List Bool) (r : Nat)
    (p : Tape u Extra) (hc : ∀ j, p ≠ .current j) (hr : ∀ j, p ≠ .remaining j) :
    stageTapes m base r p = base p := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [stageTapes]
    split
    · rw [digitOutput_frame _ _ _ _ (hc _) (hr _), ih]
    · exact ih

theorem stageTapes_current (m : Nat) (base : Tape u Extra → List Bool) (r : Nat) (j : Fin u) :
    stageTapes m base r (.current j) = if j.val < r then encodeWord 0 else base (.current j) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r, hr⟩ : Fin u)
      · subst j; simp [digitOutput]
      · rw [digitOutput_frame _ _ _ _ (by simpa using hj) (by simp), ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r + 1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r + 1 := by omega
      simp only [hjr, hjr', ite_true]

theorem stageTapes_remaining (m : Nat) (base : Tape u Extra → List Bool) (r : Nat) (j : Fin u) :
    stageTapes m base r (.remaining j) =
      if j.val < r then encodeWord (m - 1) else base (.remaining j) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r, hr⟩ : Fin u)
      · subst j; simp [digitOutput]
      · rw [digitOutput_frame _ _ _ _ (by simp) (by simpa using hj), ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r + 1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r + 1 := by omega
      simp only [hjr, hjr', ite_true]

def prefixInTime (m : Nat) (hm : 0 < m) (base : Tape u Extra → List Bool)
    (hcount : base clauseHeader = encodeWord m)
    (hcurrent : ∀ j, base (.current j) = []) (hremaining : ∀ j, base (.remaining j) = [])
    (hscratch : base .copyScratch = []) (r : Nat) (hr : r ≤ u) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨some (labelAt r), ((), none), stageTapes m base r⟩)
      (r * (2 * m + 6)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hru : r < u := by omega
    let j : Fin u := ⟨r, hru⟩
    let before := stageTapes m base r
    have one := digitInTime j m hm before
      (by dsimp only [before]; rw [stageTapes_frame _ _ _ _ (by simp [clauseHeader]) (by simp [clauseHeader])]; exact hcount)
      (by simp [before, stageTapes_current, j, hcurrent])
      (by simp [before, stageTapes_remaining, j, hremaining])
      (by dsimp only [before]; rw [stageTapes_frame _ _ _ _ (by simp) (by simp)]; exact hscratch)
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt r), ((), none), before⟩
        (some ⟨some (labelAt (r + 1)), ((), none), stageTapes m base (r + 1)⟩)
        (2 * m + 6) := by
      simpa only [labelAt, dite_eq_left hru, j, stageTapes, before] using one
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (ih (by omega)) one'
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using joined

def digitsInTime (m : Nat) (hm : 0 < m) (base : Tape u Extra → List Bool)
    (hcount : base clauseHeader = encodeWord m)
    (hcurrent : ∀ j, base (.current j) = []) (hremaining : ∀ j, base (.remaining j) = [])
    (hscratch : base .copyScratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨none, ((), none), stageTapes m base u⟩)
      (u * (2 * m + 6) + 1) := by
  have initialRun := prefixInTime m hm base hcount hcurrent hremaining hscratch u (Nat.le_refl _)
  have doneRun : StateTransition.EvalsToInTime (TM2.step (program (Extra := Extra)))
      ⟨some (labelAt u), ((), none), stageTapes m base u⟩
      (some ⟨none, ((), none), stageTapes m base u⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (labelAt u), ((), none), stageTapes m base u⟩ = _
    simp only [labelAt, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ initialRun doneRun

def outputTapes (F : Target.Formula) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  stageTapes F.clauses.length (headerOutput F base) u

def initializeInTime (F : Target.Formula) (hm : 0 < F.clauses.length)
    (base : Tape u Extra → List Bool) (hformula : base .formula = formulaBits F)
    (hwork : base .work = []) (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (hclauseHeader : base clauseHeader = [])
    (hcurrent : ∀ j, base (.current j) = []) (hremaining : ∀ j, base (.remaining j) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .inputCopyOut, ((), none), base⟩
      (some ⟨none, ((), none), outputTapes F base⟩)
      ((2 * u + 3) * (formulaBits F).length + 6 * u + 7) := by
  have firstRun := headerInTime F base hformula hwork hscratch none
  have hcount : headerOutput F base clauseHeader = encodeWord F.clauses.length := by
    simp [headerOutput, hclauseHeader]
  have secondRun := digitsInTime F.clauses.length hm (headerOutput F base) hcount
    (by intro j; rw [headerOutput_frame _ _ _ (by simp) (by simp [variableHeader])
      (by simp [clauseHeader])]; exact hcurrent j)
    (by intro j; rw [headerOutput_frame _ _ _ (by simp) (by simp [variableHeader])
      (by simp [clauseHeader])]; exact hremaining j)
    (by rw [headerOutput_frame _ _ _ (by simp) (by simp [variableHeader])
      (by simp [clauseHeader])]; exact hcopy)
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ firstRun secondRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  have hL := SourceContextLoad.clauses_length_le_input F
  have hb : u * (2 * F.clauses.length + 6) ≤ u * (2 * (formulaBits F).length + 6) :=
    Nat.mul_le_mul_left u (by omega)
  have he : (2 * u + 3) * (formulaBits F).length + 6 * u + 7 =
      u * (2 * (formulaBits F).length + 6) + 3 * (formulaBits F).length + 7 := by
    simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [he]
  omega

@[simp] theorem output_current (F : Target.Formula) (base : Tape u Extra → List Bool) (j : Fin u) :
    outputTapes F base (.current j) = encodeWord 0 := by
  simp only [outputTapes, stageTapes_current, j.isLt, ite_true]

@[simp] theorem output_remaining (F : Target.Formula) (base : Tape u Extra → List Bool) (j : Fin u) :
    outputTapes F base (.remaining j) = encodeWord (F.clauses.length - 1) := by
  simp only [outputTapes, stageTapes_remaining, j.isLt, ite_true]

theorem output_frame (F : Target.Formula) (base : Tape u Extra → List Bool) (p : Tape u Extra)
    (hw : p ≠ .work) (hn : p ≠ variableHeader) (hm : p ≠ clauseHeader)
    (hc : ∀ j, p ≠ .current j) (hr : ∀ j, p ≠ .remaining j) :
    outputTapes F base p = base p := by
  rw [outputTapes, stageTapes_frame _ _ _ _ hc hr, headerOutput_frame _ _ _ hw hn hm]

@[simp] theorem output_work (F : Target.Formula) (base : Tape u Extra → List Bool) :
    outputTapes F base .work = [] := by
  rw [outputTapes, stageTapes_frame _ _ _ _ (by simp) (by simp)]
  simp [headerOutput, variableHeader, clauseHeader]

@[simp] theorem output_variableHeader (F : Target.Formula) (base : Tape u Extra → List Bool) :
    outputTapes F base variableHeader = encodeWord F.variables ++ base variableHeader := by
  rw [outputTapes, stageTapes_frame _ _ _ _ (by simp [variableHeader]) (by simp [variableHeader])]
  simp [headerOutput, variableHeader, clauseHeader]

@[simp] theorem output_clauseHeader (F : Target.Formula) (base : Tape u Extra → List Bool) :
    outputTapes F base clauseHeader = encodeWord F.clauses.length ++ base clauseHeader := by
  rw [outputTapes, stageTapes_frame _ _ _ _ (by simp [clauseHeader]) (by simp [clauseHeader])]
  simp [headerOutput]

theorem output_headers (F : Target.Formula) (base : Tape u Extra → List Bool)
    (hn : base variableHeader = []) (hm : base clauseHeader = []) :
    outputTapes F base variableHeader = encodeWord F.variables ∧
      outputTapes F base clauseHeader = encodeWord F.clauses.length := by
  simp only [output_variableHeader, output_clauseHeader, hn, hm, List.append_nil, and_self]

@[simp] theorem output_formula (F : Target.Formula) (base : Tape u Extra → List Bool) :
    outputTapes F base .formula = base .formula :=
  output_frame F base .formula (by simp) (by simp [variableHeader])
    (by simp [clauseHeader]) (by simp) (by simp)

noncomputable def timePolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C (2 * u + 3) * Polynomial.X + Polynomial.C (6 * u + 7)

theorem timePolynomial_eval (u L : Nat) :
    (timePolynomial u).eval L = (2 * u + 3) * L + 6 * u + 7 := by
  simp [timePolynomial, Nat.add_assoc]

def machine (u : Nat) (Extra : Type) [DecidableEq Extra] [Fintype Extra] : FinTM2 where
  K := Tape u Extra
  k₀ := .formula
  k₁ := clauseHeader
  Γ _ := Bool
  Λ := Label u
  main := .inputCopyOut
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program

end BinPackingGames.Foundations.Hastad.SourceLoopInit

end OAI
