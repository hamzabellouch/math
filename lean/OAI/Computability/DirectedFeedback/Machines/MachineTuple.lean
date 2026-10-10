import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineSingleOrbitCodec

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.MachineSourceTuple

open Turing DFVSGames.Foundations.Complexity
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

theorem zeroWidthStep (base : Tape 0 Extra → List Bool) (ambient : σ) :
    TM2.step program ⟨some (labelAt 0), ((ambient, ()), none), base⟩ =
      some ⟨none, ((ambient, ()), none), base⟩ := rfl

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

end DFVSGames.Reduction.MachineSourceTuple
end

section

namespace DFVSGames.Reduction.CloneTable

open CloneGap ActualSource

variable {n : Nat}

def cloneName (v : Fin n) (i : Nat) : Fin (n * 48) :=
  ⟨i % 48 + 48 * v.val, by
    have hi := Nat.mod_lt i (show 0 < 48 by decide)
    have hv := v.isLt
    omega⟩

theorem cloneName_value (v : Fin n) (i : Nat) (hi : i < 48) :
    (cloneName v i).val = i + 48 * v.val := by
  simp only [cloneName, Nat.mod_eq_of_lt hi]

def cloneEquation (e : Equation (Fin n)) (t : Nat × Nat × Nat) :
    Equation (Fin (n * 48)) :=
  ⟨cloneName e.first t.1, cloneName e.second t.2.1,
    cloneName e.third t.2.2, e.rhs⟩

def clonedEquations (es : List (Equation (Fin n))) : List (Equation (Fin (n * 48))) :=
  es.flatMap fun e => distinctTriples.map (cloneEquation e)

private theorem length_flatMap_map_inline_CloneTable {α β γ : Type*}
    (xs : List α) (ys : List β) (f : α → β → γ) :
    (xs.flatMap fun x => ys.map (f x)).length = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
      rw [ih]
      simp [Nat.add_mul, Nat.add_comm]

theorem clonedEquations_length (es : List (Equation (Fin n))) :
    (clonedEquations es).length = es.length * distinctTriples.length := by
  exact length_flatMap_map_inline_CloneTable es distinctTriples cloneEquation

theorem clonedEquations_nonempty (es : List (Equation (Fin n))) (hne : es ≠ []) :
    clonedEquations es ≠ [] := by
  apply List.length_pos_iff.mp
  rw [clonedEquations_length]
  exact Nat.mul_pos (List.length_pos_iff.mpr hne) FiniteSource.distinctTriples_nonempty

theorem cloned_sourceList (S : Source) :
    (FiniteSource.cloned S).sourceList = clonedEquations S.sourceList := by
  let encode : Equation (Fin S.«variables» × Nat) → Equation (Fin (S.«variables» * 48)) :=
    fun e => FiniteSource.mapEquation (fun z => cloneName z.1 z.2) e
  have hmap : (FiniteSource.cloned S).sourceList = (cloneList S.sourceList).map encode := by
    have hm := congrArg (List.map encode)
      (List.ofFn_getElem (xs := cloneList S.sourceList))
    change List.ofFn (fun i : Fin (cloneList S.sourceList).length =>
      encode (cloneList S.sourceList)[i.val]) = _
    simpa only [List.map_ofFn, Function.comp_def] using hm
  rw [hmap]
  simp only [cloneList, clonedEquations, List.map_flatMap, List.map_map, Function.comp_def]
  rfl

theorem cloned_ofList_sourceList (es : List (Equation (Fin n))) (hne : es ≠ []) :
    (FiniteSource.cloned (Source.ofList es hne)).sourceList = clonedEquations es := by
  rw [cloned_sourceList, Source.sourceList_ofList]
  rfl

theorem source_reconstructed (S : Source) :
    Source.ofList S.sourceList S.sourceList_nonempty = S := by
  cases S with
  | mk n m hm eqn =>
      simp only [Source.ofList, Source.sourceList]
      erw [Source.mk.injEq]
      refine ⟨rfl, List.length_ofFn, ?_⟩
      apply (Fin.heq_fun_iff List.length_ofFn).mpr
      intro i
      simp only [List.get_eq_getElem, List.getElem_ofFn]

private theorem ofList_congr_inline_CloneTable {es fs : List (Equation (Fin n))}
    (he : es = fs) (hne : es ≠ []) (hnf : fs ≠ []) :
    Source.ofList es hne = Source.ofList fs hnf := by
  cases he
  rfl

def eraseEquation (e : Equation (Fin n)) : Equation Nat :=
  ⟨e.first.val, e.second.val, e.third.val, e.rhs⟩

def natCloneEquation (e : Equation Nat) (t : Nat × Nat × Nat) : Equation Nat :=
  ⟨t.1 + 48 * e.first, t.2.1 + 48 * e.second, t.2.2 + 48 * e.third, e.rhs⟩

def natClonedEquations (es : List (Equation Nat)) : List (Equation Nat) :=
  es.flatMap fun e => distinctTriples.map (natCloneEquation e)

theorem erase_cloneEquation (e : Equation (Fin n)) (t : Nat × Nat × Nat)
    (ht : t ∈ distinctTriples) :
    eraseEquation (cloneEquation e t) = natCloneEquation (eraseEquation e) t := by
  obtain ⟨h₁, h₂, h₃⟩ := FiniteSource.distinctTriple_bounds ht
  simp only [eraseEquation, cloneEquation, natCloneEquation, cloneName,
    Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂, Nat.mod_eq_of_lt h₃]

theorem erase_clonedEquations (es : List (Equation (Fin n))) :
    (clonedEquations es).map eraseEquation = natClonedEquations (es.map eraseEquation) := by
  simp only [clonedEquations, natClonedEquations, List.map_flatMap, List.map_map,
    List.flatMap_map, Function.comp_def]
  apply List.flatMap_congr
  intro e _
  apply List.map_congr_left
  intro t ht
  exact erase_cloneEquation e t ht

def cloneEquationWords (e : Equation (Fin n)) (t : Nat × Nat × Nat) : List Nat :=
  [t.1 + 48 * e.first.val, t.2.1 + 48 * e.second.val,
    t.2.2 + 48 * e.third.val, if e.rhs then 1 else 0]

def clonedBodyWords (es : List (Equation (Fin n))) : List Nat :=
  es.flatMap fun e => distinctTriples.flatMap (cloneEquationWords e)

theorem cloneEquation_words (e : Equation (Fin n)) (t : Nat × Nat × Nat)
    (ht : t ∈ distinctTriples) :
    SourceEncoding.equationWords (cloneEquation e t) = cloneEquationWords e t := by
  obtain ⟨h₁, h₂, h₃⟩ := FiniteSource.distinctTriple_bounds ht
  simp only [SourceEncoding.equationWords, cloneEquationWords, cloneEquation, cloneName,
    Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂, Nat.mod_eq_of_lt h₃]

theorem clonedEquations_words (es : List (Equation (Fin n))) :
    (clonedEquations es).flatMap SourceEncoding.equationWords = clonedBodyWords es := by
  simp only [clonedEquations, clonedBodyWords, List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro e _
  apply List.flatMap_congr
  intro t ht
  exact cloneEquation_words e t ht

def clonedInput (input : SourceEncoding.Input) : SourceEncoding.Input where
  «variables» := input.«variables» * 48
  equations := clonedEquations input.equations
  nonempty := clonedEquations_nonempty input.equations input.nonempty

def clonedInputWords (input : SourceEncoding.Input) : List Nat :=
  [input.«variables» * 48, input.equations.length * distinctTriples.length] ++
    clonedBodyWords input.equations

theorem clonedInput_equations (input : SourceEncoding.Input) :
    (clonedInput input).equations =
      (FiniteSource.cloned (Source.ofList input.equations input.nonempty)).sourceList := by
  exact (cloned_ofList_sourceList input.equations input.nonempty).symm

theorem clonedInput_source (input : SourceEncoding.Input) :
    Source.ofList (clonedInput input).equations (clonedInput input).nonempty =
      FiniteSource.cloned (Source.ofList input.equations input.nonempty) := by
  have hs := source_reconstructed
    (FiniteSource.cloned (Source.ofList input.equations input.nonempty))
  have he := clonedInput_equations input
  exact (ofList_congr_inline_CloneTable he _ _).trans hs

theorem clonedInput_words (input : SourceEncoding.Input) :
    SourceEncoding.inputWords (clonedInput input) = clonedInputWords input := by
  simp only [SourceEncoding.inputWords, clonedInput, clonedInputWords,
    clonedEquations_length, clonedEquations_words]

theorem clonedInput_decodes (input : SourceEncoding.Input) :
    SourceEncoding.decodeInputWords (clonedInputWords input) = some (clonedInput input) := by
  rw [← clonedInput_words]
  exact SourceEncoding.decodeInputWords_encoded _

theorem clonedInput_bits_length_le (input : SourceEncoding.Input) :
    (SourceEncoding.inputBits (clonedInput input)).length ≤
      48 * input.«variables» + distinctTriples.length * input.equations.length + 2 +
        distinctTriples.length * input.equations.length * (144 * input.«variables» + 2) := by
  calc
    _ ≤ (clonedInput input).«variables» + (clonedInput input).equations.length + 2 +
        (clonedInput input).equations.length * (3 * (clonedInput input).«variables» + 2) :=
      SourceEncoding.inputBits_length_le _
    _ = _ := by
      simp only [clonedInput, clonedEquations_length]
      ring

end DFVSGames.Reduction.CloneTable
end

section

namespace DFVSGames.Reduction.CloneMachineModel

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

inductive Tape
  | input | header | counter | field (slot : Fin 4) | scratch | reversed | output
  deriving DecidableEq, Fintype

abbrev Context (D : Nat) := Fin 2 ⊕ (Fin D × Fin 4)
abbrev State (D : Nat) := (Unit × Context D) × Option Bool
abbrev Alphabet (_ : Tape) := Bool

inductive Label (D : Nat)
  | headerStart (slot : Fin 2)
  | headerLoop (slot : Fin 2)
  | setup (context : Context D)
  | scan (context : Context D)
  | emit (context control : Context D) (symbol : Bool)
  | restore (context : Context D)
  | clearHeader
  | guard
  | fieldStart (slot : Fin 4)
  | fieldLoop (slot : Fin 4)
  | cleanup (slot : Fin 4)
  | finalCounter
  | finalReverse
  deriving DecidableEq, Fintype

def defaultControl (D : Nat) : Context D := .inl 0
def initialState (D : Nat) : State D := (((), defaultControl D), none)

def headerTape (j : Fin 2) : Tape := if j.val = 0 then .header else .counter

def contextSource {D : Nat} : Context D → Tape
  | .inl j => headerTape j
  | .inr p => .field p.2

def contextScale {D : Nat} : Context D → Nat
  | .inl j => if j.val = 0 then 48 else D
  | .inr p => if p.2.val < 3 then 48 else 1

def tripleField (t : Nat × Nat × Nat) (j : Fin 4) : Nat :=
  match j.val with
  | 0 => t.1
  | 1 => t.2.1
  | 2 => t.2.2
  | _ => 0

def contextOffset (triples : List (Nat × Nat × Nat)) : Context triples.length → Nat
  | .inl _ => 0
  | .inr p => tripleField (triples.get p.1) p.2

def affineEmit (scale offset : Nat) : Bool → List Bool
  | true => List.replicate scale true
  | false => encodeWord offset

def emission (triples : List (Nat × Nat × Nat)) (c : Context triples.length) :
    Bool → List Bool := affineEmit (contextScale c) (contextOffset triples c)

def contextNext {D : Nat} : Context D → Option (Label D)
  | .inl j => if j.val = 0 then some (.setup (.inl 1)) else some .clearHeader
  | .inr (i, j) =>
      if hj : j.val + 1 < 4 then some (.setup (.inr (i, ⟨j.val + 1, hj⟩)))
      else if hi : i.val + 1 < D then some (.setup (.inr (⟨i.val + 1, hi⟩, 0)))
      else some (.cleanup 0)

def cleanupNext {D : Nat} (j : Fin 4) : Label D :=
  if hj : j.val + 1 < 4 then .cleanup ⟨j.val + 1, hj⟩ else .guard

def drain {D : Nat} (tape : Tape) (again next : Label D) :
    TM2.Stmt Alphabet (Label D) (State D) :=
  .pop tape (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => again)
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def program (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) :
    Label triples.length → TM2.Stmt Alphabet (Label triples.length) (State triples.length)
  | .headerStart j => SourceMachine.fieldStart (headerTape j) (.headerLoop j)
  | .headerLoop j => SourceMachine.fieldLoop .input (headerTape j) (.headerLoop j)
      (if j.val = 0 then some (.headerStart 1) else some (.setup (.inl 0)))
  | .setup c => .load (fun _ => (((), c), none)) (.goto fun _ => .scan c)
  | .scan c => MachineTransducerCopy.scanLoop (contextSource c) .scratch
      (defaultControl _) (fun q b => .emit c q b) (.restore c)
  | .emit c q b => MachineTransducerCopy.emitter .reversed (fun q _ => q)
      (emission triples) (.scan c) q b
  | .restore c => MachineTransfer.loopAt .scratch (contextSource c) id false
      (.restore c) (contextNext c)
  | .clearHeader => drain .header .clearHeader .guard
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) .finalCounter
  | .fieldStart j => SourceMachine.fieldStart (.field j) (.fieldLoop j)
  | .fieldLoop j => SourceMachine.fieldLoop .input (.field j) (.fieldLoop j)
      (SourceMachine.fieldNext Label.fieldStart
        (some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0)))) j)
  | .cleanup j => drain (.field j) (.cleanup j) (cleanupNext j)
  | .finalCounter => .pop .counter (fun state _ => (state.1, none))
      (.goto fun _ => .finalReverse)
  | .finalReverse => MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label triples.length
  main := .headerStart 0
  σ := State triples.length
  initialState := initialState _
  m := program triples nonempty

end DFVSGames.Reduction.CloneMachineModel
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
