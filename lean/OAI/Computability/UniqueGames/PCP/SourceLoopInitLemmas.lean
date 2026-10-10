import OAI.Computability.UniqueGames.Machines.MachineDrainManyLemmas
import OAI.Computability.UniqueGames.PCP.SourceContextLoad
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit

open Turing UniqueGamesTheorem.Foundations.Complexity
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

end UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit

namespace UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeFinish

open Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Label (clearKeys : List K) := MachineDrainMany.Label clearKeys ⊕ Bool
abbrev Tapes (K : Type) := K → List Bool

def entry (clearKeys : List K) (labels : Label clearKeys → Λ) : Option Λ :=
  MachineDrainMany.entry clearKeys (fun l => labels (.inl l)) (some (labels (.inr false)))

/-- All instructions act on physical stacks. The final load only resets the
finite internal register; no input-dependent integer is stored in it. -/
def statement (clearKeys : List K) (accumulator output : K) (canonical : σ)
    (labels : Label clearKeys → Λ) (exit : Option Λ) :
    Label clearKeys → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .inl label => MachineDrainMany.instruction clearKeys (fun l => labels (.inl l))
      (some (labels (.inr false))) label
  | .inr false => Reduction.MachineTransfer.loopAt accumulator output id false
      (labels (.inr false)) (some (labels (.inr true)))
  | .inr true => .load (fun _ => (canonical, none)) (Reduction.MachineTransfer.exitAt output exit)

def canonicalTapes (output : K) (word : List Bool) : Tapes K :=
  Function.update (fun _ => []) output word

def finishCost (clearKeys : List K) (accumulator : K) (base : Tapes K) : Nat :=
  MachineDrainMany.steps clearKeys base + (base accumulator).length + 2

theorem cleared_frame (clearKeys : List K) (base : Tapes K) (tape : K)
    (h : tape ∉ clearKeys) : MachineDrainMany.finalTapes clearKeys base tape = base tape :=
  MachineDrainMany.finalTapes_not_mem clearKeys base tape h

theorem reversed_tapes (clearKeys : List K) (accumulator output : K)
    (distinct : accumulator ≠ output)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) :
    Reduction.MachineTransfer.tapesAt accumulator output
      (MachineDrainMany.finalTapes clearKeys base) [] (base accumulator).reverse =
      canonicalTapes output (base accumulator).reverse := by
  funext k
  by_cases hout : k = output
  · subst k
    simp [Reduction.MachineTransfer.tapesAt, canonicalTapes]
  · by_cases hacc : k = accumulator
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, canonicalTapes, distinct]
    · have hclear := MachineDrainMany.finalTapes_mem clearKeys base k (covers k hacc hout)
      simp [Reduction.MachineTransfer.tapesAt, canonicalTapes, hout, hacc, hclear]

/-- Exact execution, including the real drain loops, reversal, and reset. The
only program hypotheses identify the caller's actual placed statements. -/
def finishInTime (clearKeys : List K) (accumulator output : K)
    (distinct : accumulator ≠ output)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (canonical : σ) (labels : Label clearKeys → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ label,
      program (labels label) = statement clearKeys accumulator output canonical labels exit label)
    (base : Tapes K) (outputEmpty : base output = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry clearKeys labels, (ambient, register), base⟩
      (some ⟨exit, (canonical, none), canonicalTapes output (base accumulator).reverse⟩)
      (finishCost clearKeys accumulator base) := by
  let cleared := MachineDrainMany.finalTapes clearKeys base
  let afterRegister := MachineDrainMany.finalRegister clearKeys register
  let drain : StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry clearKeys labels, (ambient, register), base⟩
      (some ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩)
      (MachineDrainMany.steps clearKeys base) := {
    steps := MachineDrainMany.steps clearKeys base
    evals_in_steps := MachineDrainMany.trace clearKeys (fun l => labels (.inl l))
      (some (labels (.inr false))) program (fun l => atLabels (.inl l)) base ambient register
    steps_le_m := Nat.le_refl _ }
  have acc : cleared accumulator = base accumulator := cleared_frame _ _ _ keepAccumulator
  have out : cleared output = [] := (cleared_frame _ _ _ keepOutput).trans outputEmpty
  let reverse : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩
      (some ⟨some (labels (.inr true)), (ambient, none),
        canonicalTapes output (base accumulator).reverse⟩) ((base accumulator).length + 1) := {
    steps := (base accumulator).length + 1
    evals_in_steps := by
      change (Reduction.MachineTransfer.nextAt output program)^[(base accumulator).length + 1]
        (some ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩) = _
      have run := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool)
        accumulator output distinct id false (labels (.inr false))
        (some (labels (.inr true))) program
        (by simpa only [statement] using atLabels (.inr false)) cleared ambient afterRegister
      simpa only [acc, out, List.map_id, List.append_nil,
        cleared, reversed_tapes clearKeys accumulator output distinct covers base] using run
    steps_le_m := Nat.le_refl _ }
  let reset : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inr true)), (ambient, none), canonicalTapes output (base accumulator).reverse⟩
      (some ⟨exit, (canonical, none), canonicalTapes output (base accumulator).reverse⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program (labels (.inr true))) _ _) = _
      rw [atLabels]
      cases exit <;> rfl
    steps_le_m := Nat.le_refl _ }
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ drain reverse
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first reset
  have hsteps : run.steps = finishCost clearKeys accumulator base := by
    change 1 + ((base accumulator).length + 1 + MachineDrainMany.steps clearKeys base) = _
    unfold finishCost
    omega
  exact {
    steps := finishCost clearKeys accumulator base
    evals_in_steps := by simpa only [hsteps] using run.evals_in_steps
    steps_le_m := Nat.le_refl _ }

theorem finishCost_le_list (clearKeys : List K) (accumulator : K) (base : Tapes K) :
    finishCost clearKeys accumulator base ≤ MachineDrainMany.lengthSum clearKeys base +
      clearKeys.length + (base accumulator).length + 2 := by
  have h := MachineDrainMany.steps_le clearKeys base
  unfold finishCost
  omega

variable [Fintype K]
open scoped BigOperators

def totalLength (base : Tapes K) : Nat := ∑ k, (base k).length

theorem totalLength_erase (base : Tapes K) (source : K) :
    totalLength (Function.update base source []) + (base source).length = totalLength base := by
  calc
    _ = ∑ k, (((Function.update base source []) k).length +
        if k = source then (base source).length else 0) := by
      simp [totalLength, Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : k = source
      · subst k
        simp
      · simp [h]

/-- Each physical pop removes one stored symbol; repeated clear keys add only
the extra empty-tape loop test after their first occurrence. -/
theorem drain_conservation (clearKeys : List K) (base : Tapes K) :
    MachineDrainMany.steps clearKeys base +
      totalLength (MachineDrainMany.finalTapes clearKeys base) =
        totalLength base + clearKeys.length := by
  induction clearKeys generalizing base with
  | nil => simp [MachineDrainMany.steps, MachineDrainMany.finalTapes]
  | cons source rest ih =>
      have h := ih (Function.update base source [])
      have erase := totalLength_erase base source
      simp only [MachineDrainMany.steps, MachineDrainMany.finalTapes, List.length_cons]
      omega

theorem cleared_totalLength (clearKeys : List K) (accumulator output : K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) (outputEmpty : base output = []) :
    totalLength (MachineDrainMany.finalTapes clearKeys base) = (base accumulator).length := by
  have point (k : K) : (MachineDrainMany.finalTapes clearKeys base k).length =
      if k = accumulator then (base accumulator).length else 0 := by
    by_cases ha : k = accumulator
    · subst k
      simp [cleared_frame clearKeys base accumulator keepAccumulator]
    · by_cases ho : k = output
      · subst k
        simp [ha, cleared_frame clearKeys base output keepOutput, outputEmpty]
      · rw [MachineDrainMany.finalTapes_mem clearKeys base k (covers k ha ho)]
        simp [ha]
  simp only [totalLength, point]
  simp

/-- Exact finalization cost from the complete initial stack contents. -/
theorem finishCost_eq_totalLength (clearKeys : List K) (accumulator output : K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) (outputEmpty : base output = []) :
    finishCost clearKeys accumulator base = totalLength base + clearKeys.length + 2 := by
  have h := drain_conservation clearKeys base
  rw [cleared_totalLength clearKeys accumulator output keepAccumulator keepOutput covers
    base outputEmpty] at h
  unfold finishCost
  omega

end UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeFinish

end OAI
