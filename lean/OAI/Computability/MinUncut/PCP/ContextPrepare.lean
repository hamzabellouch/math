import Mathlib
import OAI.Computability.MinUncut.PCP.ProfileBridge
import OAI.Computability.MinUncut.Machines.MachineSubroutine

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceContextPrepare

open Turing MinUncutGames.Foundations.Complexity
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

abbrev Arena (u : Nat) (Extra : Type) := SourceContextLoad.Tape u Extra
abbrev LoadState := Unit × Option Bool
abbrev PrepareState (u : Nat) (τ : Type) := SourceSignaturePrepare.State u τ
abbrev State (u : Nat) (τ : Type) := LoadState × PrepareState u τ
abbrev Label (u : Nat) := SourceContextLoad.Label u ⊕ SourceSignaturePrepare.Label u

variable {u : Nat} {Extra τ : Type}

def prepareEntry (u : Nat) : SourceSignaturePrepare.Label u :=
  .profile (MachineFieldProfile.labelAt
    (MachineFieldProfile.allPairs (SourceSignaturePrepare.Width u)) 0 0)

def stateSwap (u : Nat) (τ : Type) : PrepareState u τ × LoadState ≃ State u τ :=
  Equiv.prodComm _ _

def program : Label u → TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u) (State u τ)
  | .inl l => MachineStateFrame.statement Sum.inl (some (.inr (prepareEntry u)))
      (SourceContextLoad.program l)
  | .inr l => MachineControl.statement id (stateSwap u τ)
      (MachineStateFrame.statement Sum.inr none (SourceSignaturePrepare.program l))

def preparationConfiguration (loaderState : LoadState)
    (c : TM2.Cfg (fun _ : Arena u Extra => Bool) (SourceSignaturePrepare.Label u) (PrepareState u τ)) :
    TM2.Cfg (fun _ : Arena u Extra => Bool) (Label u) (State u τ) :=
  MachineControl.configuration id (stateSwap u τ)
    (MachineStateFrame.configuration Sum.inr none loaderState c)

variable [DecidableEq Extra]

theorem preparation_step (loaderState : LoadState)
    (a b : TM2.Cfg (fun _ : Arena u Extra => Bool)
      (SourceSignaturePrepare.Label u) (PrepareState u τ))
    (h : TM2.step SourceSignaturePrepare.program a = some b) :
    TM2.step program (preparationConfiguration loaderState a) =
      some (preparationConfiguration loaderState b) := by
  rcases a with ⟨label, state, tapes⟩
  cases label with
  | none => cases h
  | some l =>
    change some (TM2.stepAux (SourceSignaturePrepare.program l) state tapes) = some b at h
    cases Option.some.inj h
    change some (TM2.stepAux
      (MachineControl.statement id (stateSwap u τ)
        (MachineStateFrame.statement Sum.inr none (SourceSignaturePrepare.program l)))
      ((stateSwap u τ) (state, loaderState)) tapes) = _
    rw [MachineControl.stepAux_simulation, MachineStateFrame.stepAux_simulation]
    rfl

def initialState (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (ambient : τ) : State u τ :=
  (((), none), (MachineFieldProfile.normalState initialProfile, (initial, ambient)))

def finalState (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (ambient : τ) : State u τ :=
  (((), none), (MachineFieldProfile.normalState (MachineFieldProfile.equalityProfile (nameWords F c)),
    (ofContext F c selected, ambient)))

noncomputable def loadInTime (F : Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (c j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl (SourceContextLoad.labelAt 0)), initialState initialProfile initial ambient, base⟩
      (some ⟨some (.inr (prepareEntry u)), initialState initialProfile initial ambient,
        SourceContextLoad.stageTapes F c base u⟩)
      (u * (10 * (formulaBits F).length + 20) + 1) := by
  have run := SourceContextLoad.loadUnaryInTime F c base hformula hcurrent
    hindex hwork hscratch hcopy
  have lifted := MachineStateFrame.execution Sum.inl (some (.inr (prepareEntry u)))
    (MachineFieldProfile.normalState initialProfile, (initial, ambient))
    SourceContextLoad.program program (fun _ => rfl) run
  simpa only [MachineStateFrame.configuration, MachineStateFrame.frameConfiguration,
    MachineSubroutine.configuration, MachineSubroutine.label, initialState] using lifted

def signatureInTime (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (base : Arena u Extra → List Bool)
    (hindex : base .index = []) (hwork : base .work = []) (hscratch : base .scratch = [])
    (hfields : ∀ p : Position u, base (SourceSignaturePrepare.variableField p) = [])
    (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (hselected : initial.selected = selected) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr (prepareEntry u)), initialState initialProfile initial ambient,
        SourceContextLoad.stageTapes F c base u⟩
      (some ⟨none, finalState F c selected ambient, SourceContextLoad.stageTapes F c base u⟩)
      (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u *
        (5 * (formulaBits F).length + 6) + 2) := by
  have run := SourceSignaturePrepare.loadedPrepareInTime F c selected base
    hindex hwork hscratch hfields initialProfile initial hselected ambient
  have lifted := MachineComposition.liftExecutionInTime
    (TM2.step SourceSignaturePrepare.program) (TM2.step program)
    (preparationConfiguration ((), none)) (preparation_step ((), none)) run
  simpa only [preparationConfiguration, MachineControl.configuration, MachineStateFrame.configuration,
    MachineStateFrame.frameConfiguration, MachineSubroutine.configuration,
    MachineSubroutine.label, Option.map_some, Option.map_none, id_eq, stateSwap,
    Equiv.prodComm_apply, Prod.swap, initialState, finalState, prepareEntry] using lifted

noncomputable def prepareInTime (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (base : Arena u Extra → List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (c j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (hfields : ∀ p : Position u, base (SourceSignaturePrepare.variableField p) = [])
    (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (hselected : initial.selected = selected) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl (SourceContextLoad.labelAt 0)), initialState initialProfile initial ambient, base⟩
      (some ⟨none, finalState F c selected ambient, SourceContextLoad.stageTapes F c base u⟩)
      ((u * (10 * (formulaBits F).length + 20) + 1) +
        (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u *
          (5 * (formulaBits F).length + 6) + 2)) := by
  have firstRun := loadInTime F c base hformula hcurrent hindex hwork hscratch hcopy
    initialProfile initial ambient
  have secondRun := signatureInTime F c selected base hindex hwork hscratch hfields
    initialProfile initial hselected ambient
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ firstRun secondRun

def machine (u : Nat) (Extra τ : Type) [DecidableEq Extra] [Fintype Extra] [Fintype τ]
    (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (ambient : τ) : FinTM2 where
  K := Arena u Extra
  k₀ := .formula
  k₁ := .formula
  Γ _ := Bool
  Λ := Label u
  main := .inl (SourceContextLoad.labelAt 0)
  σ := State u τ
  initialState := initialState initialProfile initial ambient
  m := program

end MinUncutGames.Foundations.Hastad.SourceContextPrepare

end
section

namespace MinUncutGames.Foundations.Hastad.SourceLoopInit

open Turing MinUncutGames.Foundations.Complexity
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
    [F.«variables», F.clauses.length] (encodeWords (F.clauses.flatMap clauseWords))

def headerOutput (F : Target.Formula) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  Function.update (Function.update (Function.update base .work []) variableHeader
    (encodeWord F.«variables» ++ base variableHeader)) clauseHeader
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
    (some .clearWork) program (copiedInput base) 0 [F.«variables», F.clauses.length]
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
    have he : (formulaBits F).length = F.«variables» + F.clauses.length + 2 +
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
    outputTapes F base variableHeader = encodeWord F.«variables» ++ base variableHeader := by
  rw [outputTapes, stageTapes_frame _ _ _ _ (by simp [variableHeader]) (by simp [variableHeader])]
  simp [headerOutput, variableHeader, clauseHeader]

@[simp] theorem output_clauseHeader (F : Target.Formula) (base : Tape u Extra → List Bool) :
    outputTapes F base clauseHeader = encodeWord F.clauses.length ++ base clauseHeader := by
  rw [outputTapes, stageTapes_frame _ _ _ _ (by simp [clauseHeader]) (by simp [clauseHeader])]
  simp [headerOutput]

theorem output_headers (F : Target.Formula) (base : Tape u Extra → List Bool)
    (hn : base variableHeader = []) (hm : base clauseHeader = []) :
    outputTapes F base variableHeader = encodeWord F.«variables» ∧
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

end MinUncutGames.Foundations.Hastad.SourceLoopInit

end

end OAI
