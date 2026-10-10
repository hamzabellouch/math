import Mathlib
import OAI.Computability.MinUncut.PCP.ClauseLookup
import OAI.Computability.MinUncut.Machines.MachineDrain

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceContextLoad

open Turing MinUncutGames.Foundations.Complexity
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
  have he : formulaBits F = encodeWords [F.«variables», F.clauses.length] ++
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

end MinUncutGames.Foundations.Hastad.SourceContextLoad

namespace MinUncutGames.Foundations.Hastad.SourceLocalSignature

open Target PCP SourceContexts

abbrev Position (u : ℕ) := Fin u × Slot
abbrev NameProfile (u : ℕ) := Position u → Position u → Bool

structure Signature (u : ℕ) where
  signs : Position u → Bool
  sameName : NameProfile u
  selected : SlotContext u
  deriving DecidableEq

def signatureEquiv (u : ℕ) :
    Signature u ≃ (Position u → Bool) × NameProfile u × SlotContext u where
  toFun σ := (σ.signs, σ.sameName, σ.selected)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv σ := by cases σ; rfl
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl

instance signatureFintype (u : ℕ) : Fintype (Signature u) :=
  Fintype.ofEquiv ((Position u → Bool) × NameProfile u × SlotContext u)
    (signatureEquiv u).symm

@[simp] theorem card_position (u : ℕ) : Fintype.card (Position u) = 3 * u := by
  simp [Position, Nat.mul_comm]

theorem card_signature (u : ℕ) :
    Fintype.card (Signature u) =
      2 ^ (3 * u) * ((2 ^ (3 * u)) ^ (3 * u) * 3 ^ u) := by
  rw [Fintype.card_congr (signatureEquiv u)]
  simp [NameProfile, Nat.mul_comm]

def positiveAt {n : ℕ} (clause : Clause n) : Slot → Bool
  | .first => clause[0].positive
  | .second => clause[1].positive
  | .third => clause[2].positive

def occurrenceName (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (p : Position u) : Fin F.«variables» :=
  nameAt (clauseAt F (c p.1)) p.2

def contextNameProfile (F : Formula) {u : ℕ} (c : ClauseContext F u) : NameProfile u :=
  fun p q => decide (occurrenceName F c p = occurrenceName F c q)

def ofContext (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (selected : SlotContext u) : Signature u where
  signs p := positiveAt (clauseAt F (c p.1)) p.2
  sameName := contextNameProfile F c
  selected := selected

@[simp] theorem ofContext_signs (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (p : Position u) :
    (ofContext F c s).signs p = positiveAt (clauseAt F (c p.1)) p.2 := rfl

@[simp] theorem ofContext_sameName (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (p q : Position u) :
    (ofContext F c s).sameName p q =
      decide (occurrenceName F c p = occurrenceName F c q) := rfl

@[simp] theorem ofContext_selected (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) : (ofContext F c s).selected = s := rfl

def signatureSatisfies {u : ℕ} (σ : Signature u) (j : J u) (t : Fin u) : Bool :=
  (literalValue (σ.signs (t, .first)) (j t).first ||
    literalValue (σ.signs (t, .second)) (j t).second) ||
    literalValue (σ.signs (t, .third)) (j t).third

def signatureValid {u : ℕ} (σ : Signature u) (j : J u) : Bool :=
  decide ((∀ t, signatureSatisfies σ j t = true) ∧
    ∀ t t' s s', σ.sameName (t, s) (t', s') = true →
      answerAt (j t) s = answerAt (j t') s')

@[simp] theorem signatureSatisfies_ofContext (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (j : J u) (t : Fin u) :
    signatureSatisfies (ofContext F c s) j t =
      localSatisfies (clauseAt F (c t)) (j t) := rfl

theorem signature_validJ (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (j : J u) :
    signatureValid (ofContext F c s) j = validJ F c j := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hs := of_decide_eq_true h
    apply (validJ_eq_true_iff F c j).mpr
    constructor
    · intro t
      exact (signatureSatisfies_ofContext F c s j t).symm.trans (hs.1 t)
    · intro t t' a a' hname
      apply hs.2 t t' a a'
      exact decide_eq_true hname
  · intro h
    have hs := (validJ_eq_true_iff F c j).mp h
    apply decide_eq_true
    constructor
    · intro t
      exact (signatureSatisfies_ofContext F c s j t).trans (hs.1 t)
    · intro t t' a a' heq
      exact hs.2 t t' a a' (of_decide_eq_true heq)

def signatureCanonicalSlot {u : ℕ} (σ : Signature u) (t : Fin u) : Slot :=
  if σ.sameName (t, .first) (t, σ.selected t) then .first
  else if σ.sameName (t, .second) (t, σ.selected t) then .second else .third

def signatureProjection {u : ℕ} (σ : Signature u) (j : J u) : I u :=
  fun t => answerAt (j t) (signatureCanonicalSlot σ t)

theorem signatureCanonicalSlot_ofContext (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (t : Fin u) :
    signatureCanonicalSlot (ofContext F c s) t =
      canonicalSlot (clauseAt F (c t)) (sampledVariables F c s t) := by
  by_cases hfirst : nameAt (clauseAt F (c t)) .first =
      nameAt (clauseAt F (c t)) (s t)
  · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
      occurrenceName, sampledVariables, hfirst]
  · by_cases hsecond : nameAt (clauseAt F (c t)) .second =
        nameAt (clauseAt F (c t)) (s t)
    · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
        occurrenceName, sampledVariables, hfirst, hsecond]
    · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
        occurrenceName, sampledVariables, hfirst, hsecond]

theorem signature_pi (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (j : J u) :
    signatureProjection (ofContext F c s) j = pi F c (sampledVariables F c s) j := by
  funext t
  simp only [signatureProjection, signatureCanonicalSlot_ofContext, pi]

theorem signature_projection_selected (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (j : J u)
    (hj : signatureValid (ofContext F c s) j = true) :
    signatureProjection (ofContext F c s) j = fun t => answerAt (j t) (s t) := by
  rw [signature_pi]
  have hv : validJ F c j = true := by simpa only [signature_validJ] using hj
  funext t
  exact (sampled_eq_pi F c (sampledVariables F c s) j hv t (s t) rfl).symm

theorem validJ_eq_of_signature_eq (F G : Formula) {u : ℕ}
    (c : ClauseContext F u) (d : ClauseContext G u) (s s' : SlotContext u)
    (h : ofContext F c s = ofContext G d s') (j : J u) :
    validJ F c j = validJ G d j := by
  rw [← signature_validJ F c s, h, signature_validJ]

theorem pi_eq_of_signature_eq (F G : Formula) {u : ℕ}
    (c : ClauseContext F u) (d : ClauseContext G u) (s s' : SlotContext u)
    (h : ofContext F c s = ofContext G d s') (j : J u) :
    pi F c (sampledVariables F c s) j = pi G d (sampledVariables G d s') j := by
  rw [← signature_pi F c s, h, signature_pi]

end MinUncutGames.Foundations.Hastad.SourceLocalSignature

namespace MinUncutGames.Foundations.Hastad.SourceLocalEquation

open Target SourceContexts SourceOccurrences SourceLocalSignature
open MinUncutGames.Reduction.CloneGap
open MinUncutGames.Reduction.FiniteNoise

abbrev LocalKey (u : ℕ) := Cube (I u) ⊕ (Cube (J u) ⊕ Unit)
abbrev LocalInput (u D : ℕ) := Signature u × SourceTape.TestTape (I u) (J u) D

def signatureEncoding (u : ℕ) : Encoding (Signature u) :=
  let position := (Encoding.fin u).prod slotEncoding
  let fields := (position.function Encoding.bool).prod
    ((position.function (position.function Encoding.bool)).prod (slotContextEncoding u))
  ⟨fields.size, (signatureEquiv u).trans fields.code⟩

def signatureList (u : ℕ) : List (Signature u) := (signatureEncoding u).enumerate

theorem mem_signatureList (u : ℕ) (σ : Signature u) : σ ∈ signatureList u :=
  (signatureEncoding u).mem_enumerate σ

theorem signatureList_nodup (u : ℕ) : (signatureList u).Nodup :=
  (signatureEncoding u).nodup_enumerate

theorem signatureList_length (u : ℕ) :
    (signatureList u).length = (signatureEncoding u).size :=
  (signatureEncoding u).length_enumerate

def localInputEncoding (u D : ℕ) : Encoding (LocalInput u D) :=
  (signatureEncoding u).prod (testTapeEncoding u D)

def localInputs (u D : ℕ) : List (LocalInput u D) := (localInputEncoding u D).enumerate

theorem mem_localInputs (u D : ℕ) (p : LocalInput u D) : p ∈ localInputs u D :=
  (localInputEncoding u D).mem_enumerate p

theorem localInputs_nodup (u D : ℕ) : (localInputs u D).Nodup :=
  (localInputEncoding u D).nodup_enumerate

theorem localInputs_length (u D : ℕ) :
    (localInputs u D).length = (localInputEncoding u D).size :=
  (localInputEncoding u D).length_enumerate

def localKeyEncoding (u : ℕ) : Encoding (LocalKey u) :=
  ((iEncoding u).function Encoding.bool).sum
    (((jEncoding u).function Encoding.bool).sum Encoding.unit)

def emptyLocalAddress (u : ℕ) : EmptyContext.Address (leftAnchor u) → LocalKey u
  | .inl f => .inl f.val
  | .inr _ => .inr (.inr ())

def foldedLocalAddress (u : ℕ) (valid : J u → Bool)
    (j₀ : {j : J u // valid j = true}) :
    FoldedEquation.Address (leftAnchor u) j₀ → LocalKey u
  | .inl f => .inl f.val
  | .inr g => .inr (.inl (extendRestricted valid g.val))

def equationFor (u D : ℕ) (valid : J u → Bool) (π : J u → I u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (LocalKey u) :=
  match firstValid (jEncoding u) valid with
  | none => mapEquation (emptyLocalAddress u) (EmptyContext.equation (leftAnchor u) t.1)
  | some j₀ => mapEquation (foldedLocalAddress u valid j₀)
      (FoldedEquation.conditionedEquation valid π (leftAnchor u) j₀
        t.1 t.2.2 (realizedNoise t.2.1))

def equation (u D : ℕ) (σ : Signature u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (LocalKey u) :=
  equationFor u D (signatureValid σ) (signatureProjection σ) t

def emit (u D : ℕ) (p : LocalInput u D) : Equation (LocalKey u) :=
  equation u D p.1 p.2

def addressMap (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) : LocalKey u → Fin (nBits F u)
  | .inl f => (proofEncoding F u).code (.inl (v, f))
  | .inr (.inl g) => (proofEncoding F u).code (.inr (.inl (c, g)))
  | .inr (.inr _) => dummyIndex F u

theorem mapEquation_comp {A B C : Type} (g : B → C) (f : A → B) (e : Equation A) :
    mapEquation g (mapEquation f e) = mapEquation (g ∘ f) e := rfl

theorem addressMap_emptyLocalAddress (F : Formula) (u : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u) :
    addressMap F u c v ∘ emptyLocalAddress u = emptyAddress F u v := by
  funext a
  cases a <;> rfl

theorem addressMap_foldedLocalAddress (F : Formula) (u : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u) (valid : J u → Bool)
    (j₀ : {j : J u // valid j = true}) :
    addressMap F u c v ∘ foldedLocalAddress u valid j₀ =
      localAddress (variableEncoding F u) (clauseEncoding F u) (iEncoding u) (jEncoding u)
        v c valid (leftAnchor u) j₀ := by
  funext a
  cases a <;> rfl

theorem contextEquation_eq_map_equationFor (F : Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) :
    contextEquation F u D c v t =
      mapEquation (addressMap F u c v) (equationFor u D (validJ F c) (pi F c v) t) := by
  unfold contextEquation equationFor rightAnchor
  cases h : firstValid (jEncoding u) (validJ F c) with
  | none =>
    rw [mapEquation_comp, addressMap_emptyLocalAddress]
  | some j₀ =>
    rw [mapEquation_comp, addressMap_foldedLocalAddress]
    rfl

theorem contextEquation_eq_map (F : Formula) (u D : ℕ)
    (c : ClauseContext F u) (s : SlotContext u)
    (t : SourceTape.TestTape (I u) (J u) D) :
    contextEquation F u D c (sampledVariables F c s) t =
      mapEquation (addressMap F u c (sampledVariables F c s))
        (equation u D (ofContext F c s) t) := by
  have hv : signatureValid (ofContext F c s) = validJ F c :=
    funext (signature_validJ F c s)
  have hp : signatureProjection (ofContext F c s) = pi F c (sampledVariables F c s) :=
    funext (signature_pi F c s)
  rw [equation, hv, hp]
  exact contextEquation_eq_map_equationFor F u D c (sampledVariables F c s) t

theorem sourceEquation_eq_map_emit (F : Formula) (u D : ℕ)
    (p : SourceIndex F u D) :
    sourceEquation F u D p =
      mapEquation (addressMap F u p.1.1 (sampledVariables F p.1.1 p.1.2))
        (emit u D (ofContext F p.1.1 p.1.2, p.2)) :=
  contextEquation_eq_map F u D p.1.1 p.1.2 p.2

end MinUncutGames.Foundations.Hastad.SourceLocalEquation

end OAI
