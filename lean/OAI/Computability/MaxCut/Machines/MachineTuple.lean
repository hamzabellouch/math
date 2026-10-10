import Mathlib
import OAI.Computability.MaxCut.Games.EquationLookup

namespace OAI

namespace MaxCutGames.Reduction.MachineSourceTuple

open Turing MaxCutGames.Foundations.Complexity
open SourceEncoding
open MachineComposition

inductive Tape (width : Nat) (Extra : Type)
  | source | index | work | scratch | copyScratch
  | savedIndex (coordinate : Fin width)
  | field (coordinate : Fin width) (slot : Fin 4)
  | extra (value : Extra)
  deriving DecidableEq, Fintype

inductive Label (width : Nat)
  | copyOut (coordinate : Fin width) | copyBack (coordinate : Fin width)
  | lookup (coordinate : Fin width) (localLabel : SourceEquationLookup.Label)
  | clearWork (coordinate : Fin width) | clearIndex (coordinate : Fin width)
  | done
  deriving DecidableEq, Fintype

variable {width : Nat} {Extra σ : Type}

def place (j : Fin width) : SourceEquationLookup.Tape → Tape width Extra
  | .source => .source | .index => .index | .work => .work | .scratch => .scratch
  | .field s => .field j s

theorem place_injective (j : Fin width) : Function.Injective (place (Extra := Extra) j) := by
  intro a b h
  cases a <;> cases b <;> simp_all [place]

def fill (j : Fin width) (base : Tape width Extra → List Bool)
    (localTapes : SourceEquationLookup.Tape → List Bool) : Tape width Extra → List Bool
  | .source => localTapes .source | .index => localTapes .index
  | .work => localTapes .work | .scratch => localTapes .scratch
  | .field i s => if i = j then localTapes (.field s) else base (.field i s)
  | p => base p

@[simp] theorem fill_place (j : Fin width) (base : Tape width Extra → List Bool)
    (localTapes : SourceEquationLookup.Tape → List Bool) (p : SourceEquationLookup.Tape) :
    fill j base localTapes (place j p) = localTapes p := by
  cases p <;> simp [fill, place]

@[simp] theorem fill_self (j : Fin width) (base : Tape width Extra → List Bool) :
    fill j base (base ∘ place j) = base := by
  funext p
  cases p <;> simp [fill, place]
  intro h
  subst h
  rfl

variable [DecidableEq Extra]

theorem fill_update (j : Fin width) (base : Tape width Extra → List Bool)
    (localTapes : SourceEquationLookup.Tape → List Bool) (p : SourceEquationLookup.Tape)
    (value : List Bool) :
    fill j base (Function.update localTapes p value) =
      Function.update (fill j base localTapes) (place j p) value := by
  funext k
  cases k <;> cases p <;> simp [fill, place, Function.update_apply]
  all_goals split <;> simp_all

def placedLabel (j : Fin width) : Option SourceEquationLookup.Label → Option (Label width)
  | none => some (.clearWork j)
  | some l => some (.lookup j l)

def placedConfiguration (j : Fin width) (base : Tape width Extra → List Bool)
    (c : TM2.Cfg (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool)) :
    TM2.Cfg (fun _ : Tape width Extra => Bool) (Label width) ((σ × Unit) × Option Bool) :=
  ⟨placedLabel j c.l, c.var, fill j base c.stk⟩

def placedStatement (j : Fin width) :
    TM2.Stmt (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool) →
    TM2.Stmt (fun _ : Tape width Extra => Bool) (Label width) ((σ × Unit) × Option Bool)
  | .push k f next => .push (place j k) f (placedStatement j next)
  | .peek k f next => .peek (place j k) f (placedStatement j next)
  | .pop k f next => .pop (place j k) f (placedStatement j next)
  | .load f next => .load f (placedStatement j next)
  | .branch f yes no => .branch f (placedStatement j yes) (placedStatement j no)
  | .goto f => .goto (fun state => .lookup j (f state))
  | .halt => .goto (fun _ => .clearWork j)

theorem placed_stepAux (j : Fin width) (base : Tape width Extra → List Bool)
    (q : TM2.Stmt (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool))
    (state : (σ × Unit) × Option Bool) (localTapes : SourceEquationLookup.Tape → List Bool) :
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

def nextLabel (j : Fin width) : Label width :=
  if h : j.val + 1 < width then .copyOut ⟨j.val + 1, h⟩ else .done

def program : Label width → TM2.Stmt (fun _ : Tape width Extra => Bool)
    (Label width) ((σ × Unit) × Option Bool)
  | .copyOut j => Reduction.MachineTransfer.loopAt (.savedIndex j) .copyScratch id false
      (.copyOut j) (some (.copyBack j))
  | .copyBack j => MachineCopy.forkLoop .copyScratch (.savedIndex j) .index false
      (.copyBack j) (some (.lookup j .copyOut))
  | .lookup j l => placedStatement j (SourceEquationLookup.program l)
  | .clearWork j => MachineDrain.drain .work (.clearWork j) (some (.clearIndex j))
  | .clearIndex j => MachineDrain.drain .index (.clearIndex j) (some (nextLabel j))
  | .done => .halt

theorem placed_step (j : Fin width) (base : Tape width Extra → List Bool)
    (a b : TM2.Cfg (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool))
    (h : TM2.step SourceEquationLookup.program a = some b) :
    TM2.step program (placedConfiguration j base a) =
      some (placedConfiguration j base b) := by
  cases a with
  | mk l state localTapes =>
    cases l with
    | none => contradiction
    | some l =>
      change some (TM2.stepAux (SourceEquationLookup.program l) state localTapes) = some b at h
      cases Option.some.inj h
      change some (TM2.stepAux (placedStatement j (SourceEquationLookup.program l))
        state (fill j base localTapes)) = _
      rw [placed_stepAux]

def lookupOutput (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool) : Tape width Extra → List Bool :=
  fill j base (SourceEquationLookup.outputTapes (base ∘ place j) F.equations[i.val] suffix
    (encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords)))

noncomputable def placedLookupInTime (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord i.val ++ suffix)
    (hwork : base .work = []) (hscratch : base .scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.lookup j .copyOut), ((ambient, ()), register), base⟩
      (some ⟨some (.clearWork j), ((ambient, ()), none), lookupOutput j F i base suffix⟩)
      (4 * (inputBits F).length + 8) := by
  have h := SourceEquationLookup.lookupInTime F i (base ∘ place j) suffix
    hsource hindex hwork hscratch (ambient, ()) register
  have lifted := liftExecutionInTime (TM2.step SourceEquationLookup.program) (TM2.step program)
    (placedConfiguration j base) (placed_step j base) h
  simpa only [placedConfiguration, placedLabel, fill_self,
    SourceEquationLookup.timePolynomial_eval, lookupOutput] using lifted

def copiedTapes (j : Fin width) (base : Tape width Extra → List Bool) : Tape width Extra → List Bool :=
  Function.update base .index (base (.savedIndex j))

def coordinateOutput {n : Nat} (j : Fin width) (equation : CloneGap.Equation (Fin n))
    (base : Tape width Extra → List Bool) : Tape width Extra → List Bool
  | .index | .work => []
  | .field k s => if k = j then
      encodeWord ((equationWords equation)[s.val]'(by simp)) ++ base (.field k s)
    else base (.field k s)
  | p => base p

theorem cleanup_lookupOutput (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool) :
    Function.update (Function.update
      (lookupOutput j F i (copiedTapes j base) suffix) .work []) .index [] =
      coordinateOutput j F.equations[i.val] base := by
  funext p
  cases p with
  | source => simp [lookupOutput, fill, coordinateOutput, SourceEquationLookup.output_source,
      copiedTapes, place]
  | index => simp [coordinateOutput]
  | work => simp [coordinateOutput]
  | scratch =>
    simp only [Function.update_of_ne (by simp : (Tape.scratch : Tape width Extra) ≠ .index),
      Function.update_of_ne (by simp : (Tape.scratch : Tape width Extra) ≠ .work), lookupOutput, fill,
      coordinateOutput]
    rw [SourceEquationLookup.output_frame _ _ _ _ .scratch (by simp) (by simp) (by intro s; simp)]
    simp [copiedTapes, place]
  | field k s =>
    by_cases hk : k = j
    · subst k
      simp [lookupOutput, fill, coordinateOutput, SourceEquationLookup.output_field,
        copiedTapes, place]
    · simp [lookupOutput, fill, coordinateOutput, hk, copiedTapes]
  | copyScratch => simp [lookupOutput, fill, coordinateOutput, copiedTapes]
  | savedIndex k => simp [lookupOutput, fill, coordinateOutput, copiedTapes]
  | extra k => simp [lookupOutput, fill, coordinateOutput, copiedTapes]

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_savedIndex {n : Nat} (j k : Fin width) (equation : CloneGap.Equation (Fin n))
    (base : Tape width Extra → List Bool) :
    coordinateOutput j equation base (.savedIndex k) = base (.savedIndex k) := rfl

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_field {n : Nat} (j : Fin width) (s : Fin 4)
    (equation : CloneGap.Equation (Fin n)) (base : Tape width Extra → List Bool) :
    coordinateOutput j equation base (.field j s) =
      encodeWord ((equationWords equation)[s.val]'(by simp)) ++ base (.field j s) := by
  simp [coordinateOutput]

omit [DecidableEq Extra] in
theorem coordinateOutput_other_field {n : Nat} (j k : Fin width) (s : Fin 4)
    (equation : CloneGap.Equation (Fin n)) (base : Tape width Extra → List Bool) (h : k ≠ j) :
    coordinateOutput j equation base (.field k s) = base (.field k s) := by
  simp [coordinateOutput, h]

theorem suffix_length_le_input (F : SourceEncoding.Input) (i : Nat) :
    (encodeWords ((F.equations.drop i).flatMap equationWords)).length ≤ (inputBits F).length := by
  have hs := List.take_append_drop i F.equations
  have he : inputBits F = encodeWords [F.«variables», F.equations.length] ++
      encodeWords ((F.equations.take i).flatMap equationWords) ++
      encodeWords ((F.equations.drop i).flatMap equationWords) := by
    conv_lhs => rw [inputBits, inputWords, ← hs]
    simp only [List.flatMap_append, encodeWords_append, List.append_assoc]
    rw [hs]
  rw [he, List.length_append, List.length_append]
  omega

noncomputable def coordinateInTime (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool)
    (hsource : base .source = inputBits F)
    (hsavedIndex : base (.savedIndex j) = encodeWord i.val ++ suffix)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.copyOut j), ((ambient, ()), register), base⟩
      (some ⟨some (nextLabel j), ((ambient, ()), none), coordinateOutput j F.equations[i.val] base⟩)
      (6 * (inputBits F).length + 4 * (base (.savedIndex j)).length + 20) := by
  let copied := copiedTapes j base
  let loaded := lookupOutput j F i copied suffix
  have copyRun := MachineCopy.copyInTime (.savedIndex j) .index .copyScratch
    (by simp) (by simp) (by simp) false (.copyOut j) (.copyBack j)
    (some (.lookup j .copyOut)) program rfl rfl base hcopy (ambient, ()) register
  have copied_eq : Function.update base .index (base (.savedIndex j) ++ base .index) = copied := by
    simp [copied, copiedTapes, hindex]
  rw [copied_eq] at copyRun
  have lookupRun := placedLookupInTime j F i copied suffix
    (by simpa [copied, copiedTapes] using hsource)
    (by simpa [copied, copiedTapes] using hsavedIndex)
    (by simpa [copied, copiedTapes] using hwork)
    (by simpa [copied, copiedTapes] using hscratch) ambient none
  have workRun := MachineDrain.drainInTime .work (.clearWork j) (some (.clearIndex j))
    program rfl loaded (ambient, ()) none
  have indexRun := MachineDrain.drainInTime .index (.clearIndex j) (some (nextLabel j))
    program rfl (Function.update loaded .work []) (ambient, ()) none
  have hrun := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copyRun lookupRun)
      workRun) indexRun
  have hw : loaded .work = encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords) := by
    simp [loaded, lookupOutput, fill, SourceEquationLookup.output_work]
  have hi : (Function.update loaded .work []) .index = encodeWord 0 ++ suffix := by
    simp [loaded, lookupOutput, fill, SourceEquationLookup.output_index]
  have hc : suffix.length ≤ (base (.savedIndex j)).length := by
    rw [hsavedIndex, List.length_append]
    omega
  refine { steps := hrun.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [loaded, copied, cleanup_lookupOutput] using hrun.evals_in_steps
  · apply Nat.le_trans hrun.steps_le_m
    rw [hw, hi, List.length_append, encodeWord_length]
    have hs := suffix_length_le_input F (i.val + 1)
    omega

def labelAt (r : Nat) : Label width :=
  if h : r < width then .copyOut ⟨r, h⟩ else .done

theorem nextLabel_eq (j : Fin width) : nextLabel j = labelAt (j.val + 1) := rfl

def stageTapes (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) : Nat → Tape width Extra → List Bool
  | 0 => base
  | r + 1 => if h : r < width then
      coordinateOutput ⟨r, h⟩ F.equations[(tuple ⟨r, h⟩).val] (stageTapes F tuple base r)
    else stageTapes F tuple base r

omit [DecidableEq Extra] in
theorem stageTapes_frame (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (r : Nat) (p : Tape width Extra)
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
theorem stageTapes_clean (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (r : Nat) (hi : base .index = []) (hw : base .work = []) :
    stageTapes F tuple base r .index = [] ∧ stageTapes F tuple base r .work = [] := by
  induction r with
  | zero => exact ⟨hi, hw⟩
  | succ r ih =>
    simp only [stageTapes]
    split
    · exact ⟨rfl, rfl⟩
    · exact ih

omit [DecidableEq Extra] in
theorem stageTapes_field (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (r : Nat) (j : Fin width) (s : Fin 4) :
    stageTapes F tuple base r (.field j s) = if j.val < r then
      encodeWord ((equationWords F.equations[(tuple j).val])[s.val]'(by simp)) ++ base (.field j s)
      else base (.field j s) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r, hr⟩ : Fin width)
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

noncomputable def prefixInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : Fin width → List Bool) (C : Nat)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.savedIndex j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (r : Nat) (hr : r ≤ width) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨some (labelAt r), ((ambient, ()), none), stageTapes F tuple base r⟩)
      (r * (6 * (inputBits F).length + 4 * C + 20)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hru : r < width := by omega
    let j : Fin width := ⟨r, hru⟩
    let before := stageTapes F tuple base r
    have hf (p : Tape width Extra) (hi : p ≠ .index) (hw : p ≠ .work)
        (hh : ∀ j s, p ≠ .field j s) : before p = base p :=
      stageTapes_frame F tuple base r p hi hw hh
    have hd := stageTapes_clean F tuple base r hindex hwork
    have hc : before (.savedIndex j) = base (.savedIndex j) := hf _ (by simp) (by simp) (by simp)
    have one := coordinateInTime j F (tuple j) before (suffix j)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hsource)
      (by rw [hc]; exact hsavedIndex j) hd.1 hd.2
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hscratch)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hcopy) ambient none
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt r), ((ambient, ()), none), before⟩
        (some ⟨some (labelAt (r + 1)), ((ambient, ()), none), stageTapes F tuple base (r + 1)⟩)
        (6 * (inputBits F).length + 4 * C + 20) := by
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

noncomputable def loadInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : Fin width → List Bool) (C : Nat)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.savedIndex j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (6 * (inputBits F).length + 4 * C + 20) + 1) := by
  have prefixRun := prefixInTime F tuple base suffix C hsource hsavedIndex hsize
    hindex hwork hscratch hcopy width (Nat.le_refl _) ambient
  have doneRun : StateTransition.EvalsToInTime (TM2.step (program (Extra := Extra)))
      ⟨some (labelAt width), ((ambient, ()), none), stageTapes F tuple base width⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (labelAt width), ((ambient, ()), none), stageTapes F tuple base width⟩ = _
    simp only [labelAt, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ prefixRun doneRun

theorem equations_length_le_input (F : SourceEncoding.Input) :
    F.equations.length ≤ (inputBits F).length := by
  simp only [inputBits, encodeWords_length, inputWords_length]
  omega

/-- Actual odometer digits have empty suffixes. The resulting complete loader
runs in a polynomial whose coefficients depend only on the fixed repetition k. -/
noncomputable def loadUnaryInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (10 * (inputBits F).length + 20) + 1) := by
  have run := loadInTime F tuple base (fun _ => []) (inputBits F).length hsource
    (by simpa only [List.append_nil] using hsavedIndex)
    (by
      intro j
      rw [hsavedIndex j, encodeWord_length]
      have h := (tuple j).isLt
      have hm := equations_length_le_input F
      omega)
    hindex hwork hscratch hcopy ambient
  have he : 6 * (inputBits F).length + 4 * (inputBits F).length + 20 =
      10 * (inputBits F).length + 20 := by omega
  simpa only [he] using run

noncomputable def timePolynomial (width : Nat) : Polynomial Nat :=
  Polynomial.C (10 * width) * Polynomial.X + Polynomial.C (20 * width + 1)

theorem timePolynomial_eval (width L : Nat) :
    (timePolynomial width).eval L = width * (10 * L + 20) + 1 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]

/-- Total physical length of the saved occurrence-ID tapes. -/
def tupleBitLength (base : Tape width Extra → List Bool) : Nat :=
  ∑ j : Fin width, (base (.savedIndex j)).length

omit [DecidableEq Extra] in
theorem savedIndex_length_le_tupleBitLength (base : Tape width Extra → List Bool)
    (j : Fin width) : (base (.savedIndex j)).length ≤ tupleBitLength base := by
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (base (.savedIndex i)).length)
    (Finset.mem_univ j)

noncomputable def loadTupleInTime (F : SourceEncoding.Input)
    (tuple : Fin width → Fin F.equations.length) (base : Tape width Extra → List Bool)
    (hsource : base .source = inputBits F)
    (hsaved : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (6 * (inputBits F).length + 4 * tupleBitLength base + 20) + 1) :=
  loadInTime F tuple base (fun _ => []) (tupleBitLength base) hsource
    (by simpa only [List.append_nil] using hsaved)
    (savedIndex_length_le_tupleBitLength base) hindex hwork hscratch hcopy ambient

/-- The same concrete run with a univariate polynomial in the combined size. -/
noncomputable def loadTuplePolynomialInTime (F : SourceEncoding.Input)
    (tuple : Fin width → Fin F.equations.length) (base : Tape width Extra → List Bool)
    (hsource : base .source = inputBits F)
    (hsaved : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩)
      ((timePolynomial width).eval ((inputBits F).length + tupleBitLength base)) := by
  let run := loadTupleInTime F tuple base hsource hsaved hindex hwork hscratch hcopy ambient
  refine {
    steps := run.steps
    evals_in_steps := run.evals_in_steps
    steps_le_m := run.steps_le_m.trans ?_ }
  rw [timePolynomial_eval]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left width (by omega)) 1

def nameSlot (s : Fin 3) : Fin 4 := ⟨s.val, by omega⟩
def nameField (j : Fin width) (s : Fin 3) : Tape width Extra := .field j (nameSlot s)
def rhsField (j : Fin width) : Tape width Extra := .field j 3

omit [DecidableEq Extra] in
theorem nameField_ne_rhsField (j k : Fin width) (s : Fin 3) :
    nameField (Extra := Extra) j s ≠ rhsField k := by
  intro h
  have hv := congrArg (fun t : Tape width Extra =>
    match t with | .field _ slot => slot.val | _ => 4) h
  simp only [nameField, rhsField, nameSlot] at hv
  have hs := s.isLt
  omega

def equationName {n : Nat} (e : CloneGap.Equation (Fin n)) (s : Fin 3) : Nat :=
  match s.val with
  | 0 => e.first.val
  | 1 => e.second.val
  | _ => e.third.val

theorem equationWords_name {n : Nat} (e : CloneGap.Equation (Fin n)) (s : Fin 3) :
    (equationWords e)[(nameSlot s).val]'(by simp) = equationName e s := by
  obtain ⟨s, hs⟩ := s
  have h : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases h with rfl | rfl | rfl <;> rfl

omit [DecidableEq Extra] in
theorem output_name (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (j : Fin width) (s : Fin 3) :
    stageTapes F tuple base width (nameField j s) =
      encodeWord (equationName F.equations[(tuple j).val] s) ++ base (nameField j s) := by
  rw [nameField, stageTapes_field, ite_eq_left j.isLt, equationWords_name]

omit [DecidableEq Extra] in
theorem output_rhs (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (j : Fin width) :
    stageTapes F tuple base width (rhsField j) =
      encodeWord (if F.equations[(tuple j).val].rhs then 1 else 0) ++ base (rhsField j) := by
  rw [rhsField, stageTapes_field, ite_eq_left j.isLt]
  rfl

omit [DecidableEq Extra] in
theorem output_savedIndex (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (j : Fin width) :
    stageTapes F tuple base width (.savedIndex j) = base (.savedIndex j) :=
  stageTapes_frame F tuple base width (.savedIndex j) (by simp) (by simp) (by simp)

omit [DecidableEq Extra] in
theorem output_savedIndex_unary (F : SourceEncoding.Input)
    (tuple : Fin width → Fin F.equations.length) (base : Tape width Extra → List Bool)
    (hsaved : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val) (j : Fin width) :
    stageTapes F tuple base width (.savedIndex j) = encodeWord (tuple j).val :=
  (output_savedIndex F tuple base j).trans (hsaved j)

omit [DecidableEq Extra] in
theorem output_source (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) :
    stageTapes F tuple base width .source = base .source :=
  stageTapes_frame F tuple base width .source (by simp) (by simp) (by simp)

/-- The fourth canonical record field is the saved occurrence ID. The equation
RHS remains separately available on `rhsField j`. -/
def canonicalFields (tapes : Tape width Extra → List Bool) (j : Fin width) : List (List Bool) :=
  [tapes (nameField j 0), tapes (nameField j 1), tapes (nameField j 2), tapes (.savedIndex j)]

def canonicalWords {n : Nat} (e : CloneGap.Equation (Fin n)) (occurrence : Nat) : List Nat :=
  [e.first.val, e.second.val, e.third.val, occurrence]

omit [DecidableEq Extra] in
theorem output_canonicalFields (F : SourceEncoding.Input)
    (tuple : Fin width → Fin F.equations.length) (base : Tape width Extra → List Bool)
    (hsaved : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val)
    (hempty : ∀ j s, base (nameField j s) = []) (j : Fin width) :
    canonicalFields (stageTapes F tuple base width) j =
      (canonicalWords F.equations[(tuple j).val] (tuple j).val).map encodeWord := by
  simp [canonicalFields, output_name, output_savedIndex, hsaved, hempty,
    canonicalWords, equationName]

/-- Width zero executes its actual done statement in one transition. -/
theorem zeroWidthStep (base : Tape 0 Extra → List Bool) (ambient : σ) :
    TM2.step program ⟨some (labelAt 0), ((ambient, ()), none), base⟩ =
      some ⟨none, ((ambient, ()), none), base⟩ := rfl

/-- A caller shares this complete tape arena and state, mapping only labels and
the final continuation. All saved occurrence IDs remain available to its body. -/
noncomputable def placedLoadUnaryInTime {Λ : Type}
    (labels : Label width → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape width Extra => Bool) Λ ((σ × Unit) × Option Bool))
    (atLabels : ∀ l, target (labels l) = MachineSubroutine.statement labels exit (program l))
    (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool)
    (hsource : base .source = inputBits F)
    (hsaved : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (labelAt 0)), ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (10 * (inputBits F).length + 20) + 1) :=
  MachineSubroutine.execution labels exit program target atLabels
    (loadUnaryInTime F tuple base hsource hsaved hindex hwork hscratch hcopy ambient)

def machine (width : Nat) (Extra : Type) [DecidableEq Extra] [Fintype Extra] : FinTM2 where
  K := Tape width Extra
  k₀ := .source
  k₁ := .source
  Γ _ := Bool
  Λ := Label width
  main := labelAt 0
  σ := (Unit × Unit) × Option Bool
  initialState := (((), ()), none)
  m := program (σ := Unit)

end MaxCutGames.Reduction.MachineSourceTuple

end OAI
