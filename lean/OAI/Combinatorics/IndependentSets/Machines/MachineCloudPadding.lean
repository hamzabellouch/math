import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineCloudCount
import OAI.Combinatorics.IndependentSets.Machines.MachineCeilingPower

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineCloudPadding

open Turing
open MachineComposition
open IndependentSetsGames.Foundations.PCP

namespace Placement

variable {K K' Λ Λ' σ : Type}

def tapes (view : K' → Option K) (source : K → List Bool)
    (extra : K' → List Bool) : K' → List Bool :=
  fun j => match view j with
    | some k => source k
    | none => extra j

def label (labels : Λ → Λ') (exit : Option Λ') : Option Λ → Option Λ'
  | some l => some (labels l)
  | none => exit

def configuration (view : K' → Option K) (labels : Λ → Λ') (exit : Option Λ')
    (extra : K' → List Bool) (c : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : K' => Bool) Λ' σ :=
  ⟨label labels exit c.l, c.var, tapes view c.stk extra⟩

def statement (tape : K → K') (labels : Λ → Λ') (exit : Option Λ') :
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K' => Bool) Λ' σ
  | .push k f next => .push (tape k) f (statement tape labels exit next)
  | .peek k f next => .peek (tape k) f (statement tape labels exit next)
  | .pop k f next => .pop (tape k) f (statement tape labels exit next)
  | .load f next => .load f (statement tape labels exit next)
  | .branch f yes no => .branch f (statement tape labels exit yes) (statement tape labels exit no)
  | .goto f => .goto (fun state => labels (f state))
  | .halt => match exit with
    | some l => .goto (fun _ => l)
    | none => .halt

variable [DecidableEq K] [DecidableEq K']

omit [DecidableEq K] [DecidableEq K'] in
theorem tapes_apply (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (source : K → List Bool) (extra : K' → List Bool) (k : K) :
    tapes view source extra (tape k) = source k := by
  simp only [tapes, left]

theorem tapes_update (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (source : K → List Bool) (extra : K' → List Bool) (k : K) (w : List Bool) :
    tapes view (Function.update source k w) extra =
      Function.update (tapes view source extra) (tape k) w := by
  funext j
  by_cases h : j = tape k
  · subst j
    simp [tapes, left]
  · cases hv : view j with
    | none => simp [tapes, hv, h]
    | some i =>
      have hi : i ≠ k := by
        intro hi
        subst i
        exact h (right j k hv).symm
      simp [tapes, hv, h, hi]

theorem stepAux_simulation (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (extra : K' → List Bool)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (source : K → List Bool) :
    TM2.stepAux (statement tape labels exit q) state (tapes view source extra) =
      configuration view labels exit extra (TM2.stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    simp only [statement, TM2.stepAux, tapes_apply tape view left]
    rw [← tapes_update tape view left right]
    exact ih state (Function.update source k (f state :: source k))
  | peek k f next ih =>
    simpa only [statement, TM2.stepAux, tapes_apply tape view left] using
      ih (f state (source k).head?) source
  | pop k f next ih =>
    simp only [statement, TM2.stepAux, tapes_apply tape view left]
    rw [← tapes_update tape view left right]
    exact ih (f state (source k).head?) (Function.update source k (source k).tail)
  | load f next ih => simpa only [statement, TM2.stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, TM2.stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, TM2.stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => cases exit <;> rfl

theorem step_simulation (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement tape labels exit (source l))
    (a b : TM2.Cfg (fun _ : K => Bool) Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration view labels exit extra a) =
      some (configuration view labels exit extra b) := by
  cases a with
  | mk l state sourceTapes =>
    cases l with
    | none => simp [TM2.step] at h
    | some l =>
      have hb : TM2.stepAux (source l) state sourceTapes = b := Option.some.inj h
      rw [← hb]
      change some (TM2.stepAux (target (labels l)) state (tapes view sourceTapes extra)) = _
      rw [atLabels, stepAux_simulation tape view left right]

theorem trace (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement tape labels exit (source l))
    (n : Nat) (a b : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (run : (advance (TM2.step source))^[n] (some a) = some b) :
    (advance (TM2.step target))^[n]
      (some (configuration view labels exit extra a)) =
      some (configuration view labels exit extra b) :=
  liftSuccessfulTrace _ _ _
    (step_simulation tape view left right labels exit extra source target atLabels) n a b run

end Placement

inductive Tape
  | table | query | count | work | scratch | spare | power | level | fuel | product
  deriving DecidableEq

instance : Fintype Tape where
  elems := {.table, .query, .count, .work, .scratch, .spare, .power, .level, .fuel, .product}
  complete value := by cases value <;> simp

inductive Label
  | init | countCode (l : MachineCloudCount.Label)
  | branch | powerCode (l : MachineCeilingPower.Label)
  | subtract | restore
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def memory (table query count work scratch spare power level fuel product : List Bool) :
    Tape → List Bool
  | .table => table
  | .query => query
  | .count => count
  | .work => work
  | .scratch => scratch
  | .spare => spare
  | .power => power
  | .level => level
  | .fuel => fuel
  | .product => product

@[simp] theorem update_count (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .count x = memory a b x d e f g h i j := by
  funext k; cases k <;> rfl
@[simp] theorem update_scratch (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .scratch x = memory a b c d x f g h i j := by
  funext k; cases k <;> rfl
@[simp] theorem update_power (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .power x = memory a b c d e f x h i j := by
  funext k; cases k <;> rfl

@[simp] theorem update_level (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .level x = memory a b c d e f g x i j := by
  funext k; cases k <;> rfl

def countTape : MachineCloudCount.Tape → Tape
  | .original => .table
  | .target => .query
  | .count => .count
  | .work => .work
  | .scratch => .scratch
  | .spare => .spare

def countView : Tape → Option MachineCloudCount.Tape
  | .table => some .original
  | .query => some .target
  | .count => some .count
  | .work => some .work
  | .scratch => some .scratch
  | .spare => some .spare
  | _ => none

theorem countView_left (k : MachineCloudCount.Tape) : countView (countTape k) = some k := by
  cases k <;> rfl
theorem countView_right (j : Tape) (k : MachineCloudCount.Tape)
    (h : countView j = some k) : countTape k = j := by
  cases j <;> cases k <;> simp_all [countView, countTape]

def powerTape : MachineCeilingPower.Tape → Tape
  | .input => .count
  | .work => .work
  | .power => .power
  | .saved => .scratch
  | .level => .level
  | .fuel => .fuel
  | .spare => .spare
  | .product => .product

def powerView : Tape → Option MachineCeilingPower.Tape
  | .count => some .input
  | .work => some .work
  | .power => some .power
  | .scratch => some .saved
  | .level => some .level
  | .fuel => some .fuel
  | .spare => some .spare
  | .product => some .product
  | _ => none

theorem powerView_left (k : MachineCeilingPower.Tape) : powerView (powerTape k) = some k := by
  cases k <;> rfl
theorem powerView_right (j : Tape) (k : MachineCeilingPower.Tape)
    (h : powerView j = some k) : powerTape k = j := by
  cases j <;> cases k <;> simp_all [powerView, powerTape]

@[simp] theorem countMemory (a b c d e f g h i j : List Bool) :
    Placement.tapes countView (MachineCloudCount.memory a d b e c f)
      (memory a b c d e f g h i j) = memory a b c d e f g h i j := by
  funext k; cases k <;> rfl

@[simp] theorem powerMemory (a b c d e f g h i j : List Bool) :
    Placement.tapes powerView (MachineCeilingPower.memory c d g e h i f j)
      (memory a b c d e f g h i j) = memory a b c d e f g h i j := by
  funext k; cases k <;> rfl

theorem countTapes (a b c d e f : List Bool) (extra : Tape → List Bool) :
    Placement.tapes countView (MachineCloudCount.memory a d b e c f) extra =
      memory a b c d e f (extra .power) (extra .level) (extra .fuel) (extra .product) := by
  funext k; cases k <;> rfl

theorem powerTapes (c d g e h i f j : List Bool) (extra : Tape → List Bool) :
    Placement.tapes powerView (MachineCeilingPower.memory c d g e h i f j) extra =
      memory (extra .table) (extra .query) c d e f g h i j := by
  funext k; cases k <;> rfl

variable {σ : Type}

def subtractLoop : TM2.Stmt Alphabet Label (State σ) :=
  .pop .count (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop .power (fun state _ => (state.1, none))
        (.push .scratch (fun _ => true) (.goto fun _ => .subtract)))
      (.push .count (fun _ => false)
        (.load (fun state => (state.1, none)) (.goto fun _ => .restore))))

def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push .count (fun _ => false) (.goto fun _ => .countCode .copyFirst)
  | .countCode l => Placement.statement countTape Label.countCode (some .branch)
      (MachineCloudCount.program l)
  | .branch => .peek .count (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.load (fun state => (state.1, none)) (.goto fun _ => .powerCode .init))
        (.push .power (fun _ => false) (.push .level (fun _ => false)
          (.load (fun state => (state.1, none)) .halt))))
  | .powerCode l => Placement.statement powerTape Label.powerCode (some .subtract)
      (MachineCeilingPower.program ExpanderFamily.growth l)
  | .subtract => subtractLoop
  | .restore => Reduction.MachineTransfer.loopAt
      .scratch .count id false .restore none

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

theorem countTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineCloudCount.totalSteps t.vertices t.darts v.val
      (MachineCloudCount.tableRows t)]
      (some ⟨some (.countCode .copyFirst), ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord 0) [] [] [] [] [] [] []⟩) =
      some ⟨some .branch, ((ambient, false), none),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord (PreprocessingCloudIndex.cloudSize t v)) [] [] [] [] [] [] []⟩ := by
  have h := Placement.trace countTape countView countView_left countView_right
    Label.countCode (some Label.branch) (fun _ => [])
    (MachineCloudCount.program (σ := σ)) program (fun _ => rfl) _ _ _
    (MachineCloudCount.cloudCountTrace t v suffix [] ambient register)
  simpa only [Placement.configuration, Placement.label, countTapes, List.append_nil] using h

theorem powerTrace (table query : List Bool) (k : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step program))^[MachineCeilingPower.totalTime ExpanderFamily.growth k]
      (some ⟨some (.powerCode .init), ((ambient, false), register),
        memory table query (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨some .subtract, ((ambient, false), none),
        memory table query (encodeWord k) [] [] []
          (encodeWord (PreprocessingLevels.paddedSize k))
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] []⟩ := by
  have h := Placement.trace powerTape powerView powerView_left powerView_right
    Label.powerCode (some Label.subtract) (memory table query [] [] [] [] [] [] [] [])
    (MachineCeilingPower.program ExpanderFamily.growth (σ := σ)) program (fun _ => rfl)
    _ _ _ (MachineCeilingPower.paddingTrace k ambient register)
  simpa only [Placement.configuration, Placement.label, powerTapes, memory] using h

theorem subtractStep_zero (table query level saved : List Bool) (p : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord 0) [] saved [] (encodeWord p) level [] []⟩ =
      some ⟨some .restore, ((ambient, false), none),
        memory table query (encodeWord 0) [] saved [] (encodeWord p) level [] []⟩ := by
  change some (TM2.stepAux subtractLoop _ _) = _
  simp [subtractLoop, TM2.stepAux, memory, encodeWord]

theorem subtractStep_succ (table query level saved : List Bool) (k p : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord (k + 1)) [] saved [] (encodeWord (p + 1)) level [] []⟩ =
      some ⟨some .subtract, ((ambient, false), none),
        memory table query (encodeWord k) [] (true :: saved) [] (encodeWord p) level [] []⟩ := by
  change some (TM2.stepAux subtractLoop _ _) = _
  simp [subtractLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

theorem subtractScanTrace (table query level : List Bool) (k p : Nat)
    (saved : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[k + 1]
      (some ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord k) [] saved [] (encodeWord (k + p)) level [] []⟩) =
      some ⟨some .restore, ((ambient, false), none),
        memory table query (encodeWord 0) [] (List.replicate k true ++ saved) []
          (encodeWord p) level [] []⟩ := by
  induction k generalizing saved register with
  | zero => simpa only [Nat.zero_add, Function.iterate_one, advance_some,
      List.replicate_zero, List.nil_append] using
      subtractStep_zero table query level saved p ambient register
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    simp only [Nat.succ_add]
    change (advance (TM2.step program))^[k + 1]
      (TM2.step program ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord (k + 1)) [] saved []
          (encodeWord ((k + p) + 1)) level [] []⟩) = _
    rw [subtractStep_succ]
    simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using
      ih (true :: saved) none

theorem subtractTrace (table query level : List Bool) (k p : Nat) (hkp : k ≤ p)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * k + 2]
      (some ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord k) [] [] [] (encodeWord p) level [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory table query (encodeWord k) [] [] [] (encodeWord (p - k)) level [] []⟩ := by
  have hs := subtractScanTrace table query level k (p - k) [] ambient register
  rw [show k + (p - k) = p by omega] at hs
  simp only [List.append_nil] at hs
  let mid := memory table query (encodeWord 0) [] (List.replicate k true) []
    (encodeWord (p - k)) level [] []
  have hr := Reduction.MachineTransfer.transferAt_fromTapes Tape.scratch Tape.count (by decide)
    id false Label.restore none program rfl mid (ambient, false) none
  simp only [mid, memory, List.length_replicate, List.reverse_replicate, List.map_id,
    Reduction.MachineTransfer.tapesAt, update_scratch, update_count] at hr
  rw [MachineCeilingPower.replicate_encodeWord, Nat.add_zero] at hr
  have h := appendTrace _ hs hr
  simpa only [show (k + 1) + (k + 1) = 2 * k + 2 by omega, Nat.add_zero] using h

theorem branchStep_zero (table query : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .branch, ((ambient, false), register),
        memory table query (encodeWord 0) [] [] [] [] [] [] []⟩ =
      some ⟨none, ((ambient, false), none),
        memory table query (encodeWord 0) [] [] [] (encodeWord 0) (encodeWord 0) [] []⟩ := by
  simp [TM2.step, program, TM2.stepAux, memory, encodeWord]

theorem branchStep_succ (table query : List Bool) (k : Nat) (ambient : σ)
    (register : Option Bool) :
    TM2.step program
      ⟨some .branch, ((ambient, false), register),
        memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩ =
      some ⟨some (.powerCode .init), ((ambient, false), none),
        memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩ := by
  simp [TM2.step, program, TM2.stepAux, memory, encodeWord, List.replicate_succ]

def padding (k : Nat) : Nat := PreprocessingLevels.cloudPaddedSize k - k

def postTime (k : Nat) : Nat :=
  1 + if k = 0 then 0 else MachineCeilingPower.totalTime ExpanderFamily.growth k + (2 * k + 2)

theorem postTrace (table query : List Bool) (k : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step program))^[postTime k]
      (some ⟨some .branch, ((ambient, false), register),
        memory table query (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory table query (encodeWord k) [] [] [] (encodeWord (padding k))
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] []⟩ := by
  cases k with
  | zero =>
    simpa only [postTime, ite_eq_left rfl, ite_true, Nat.add_zero, Function.iterate_one, advance_some,
      padding, PreprocessingLevels.cloudPaddedSize_zero, Nat.sub_zero,
      PreprocessingLevels.boundedLevel_zero] using branchStep_zero table query ambient register
  | succ k =>
    have hb : (advance (TM2.step program))^[1]
        (some ⟨some .branch, ((ambient, false), register),
          memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩) =
        some ⟨some (.powerCode .init), ((ambient, false), none),
          memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩ :=
      branchStep_succ table query k ambient register
    have hp := powerTrace table query (k + 1) ambient none
    have hs := subtractTrace table query (encodeWord (PreprocessingLevels.boundedLevel (k + 1)))
      (k + 1) (PreprocessingLevels.paddedSize (k + 1))
      (PreprocessingLevels.le_paddedSize (k + 1)) ambient none
    have h := appendTrace _ hb (appendTrace _ hp hs)
    simpa only [postTime, Nat.succ_ne_zero, ite_false, padding,
      PreprocessingLevels.cloudPaddedSize_of_pos (Nat.succ_pos k)] using h

theorem initStep (table query : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .init, ((ambient, false), register), memory table query [] [] [] [] [] [] [] []⟩ =
      some ⟨some (.countCode .copyFirst), ((ambient, false), register),
        memory table query (encodeWord 0) [] [] [] [] [] [] []⟩ := by
  simp [TM2.step, program, TM2.stepAux, memory, encodeWord]

def totalTime (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  (1 + MachineCloudCount.totalSteps t.vertices t.darts v.val (MachineCloudCount.tableRows t)) +
    postTime (PreprocessingCloudIndex.cloudSize t v)

theorem cloudPaddingTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime t v]
      (some ⟨some .init, ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix) [] [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord (PreprocessingCloudIndex.cloudSize t v)) [] [] []
          (encodeWord (padding (PreprocessingCloudIndex.cloudSize t v)))
          (encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))
          [] []⟩ := by
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some .init, ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix) [] [] [] [] [] [] [] []⟩) =
      some ⟨some (.countCode .copyFirst), ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord 0) [] [] [] [] [] [] []⟩ :=
    initStep _ _ ambient register
  exact appendTrace _ (appendTrace _ hi (countTrace t v suffix ambient register))
    (postTrace _ _ (PreprocessingCloudIndex.cloudSize t v) ambient none)

def inputLength (t : GraphTables.Table) (v : Fin t.vertices) (suffix : List Bool) : Nat :=
  (GraphTables.tableBits t).length + (encodeWord v.val ++ suffix).length

theorem count_length_le (t : GraphTables.Table) (v : Fin t.vertices) (suffix : List Bool) :
    PreprocessingCloudIndex.cloudSize t v + 1 ≤ inputLength t v suffix := by
  have h := (PreprocessingCloudIndex.cloudSize_le_darts t v).trans
    (GraphTables.darts_le_tableBits_length t)
  simp only [inputLength, List.length_append, encodeWord_length]
  omega

theorem table_length_le (t : GraphTables.Table) (v : Fin t.vertices) (suffix : List Bool) :
    (GraphTables.tableBits t).length ≤ inputLength t v suffix := by
  unfold inputLength
  omega

theorem postTime_le (k : Nat) :
    postTime k ≤ 1 + MachineCeilingPower.timeBound ExpanderFamily.growth k + (2 * k + 2) := by
  have h := MachineCeilingPower.totalTime_le ExpanderFamily.growth k
  unfold postTime
  split_ifs <;> omega

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C (ExpanderFamily.growth + 8) * Polynomial.X ^ 2 + 25 * Polynomial.X + 10

theorem totalTime_le (t : GraphTables.Table) (v : Fin t.vertices) (suffix : List Bool) :
    totalTime t v ≤ timePolynomial.eval (inputLength t v suffix) := by
  have hc := MachineCloudCount.totalSteps_le t.vertices t.darts v.val (MachineCloudCount.tableRows t)
  rw [MachineCloudCount.tableRows_input] at hc
  have hp := postTime_le (PreprocessingCloudIndex.cloudSize t v)
  have hk := count_length_le t v suffix
  have ht := table_length_le t v suffix
  have hsq := Nat.mul_le_mul_left (ExpanderFamily.growth + 8)
    (Nat.pow_le_pow_left hk 2)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
  unfold MachineCeilingPower.timeBound at hp
  unfold totalTime
  omega

def cloudPaddingInTime (t : GraphTables.Table) (v : Fin t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .init, ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix) [] [] [] [] [] [] [] []⟩
      (some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord (PreprocessingCloudIndex.cloudSize t v)) [] [] []
          (encodeWord (padding (PreprocessingCloudIndex.cloudSize t v)))
          (encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))
          [] []⟩)
      (timePolynomial.eval (inputLength t v suffix)) where
  steps := totalTime t v
  evals_in_steps := cloudPaddingTrace t v suffix ambient register
  steps_le_m := totalTime_le t v suffix

theorem count_add_padding (k : Nat) : k + padding k = PreprocessingLevels.cloudPaddedSize k := by
  have h := (PreprocessingLevels.cloudPaddedSize_bounds k).1
  unfold padding
  omega

end IndependentSetsGames.Foundations.Complexity.MachineCloudPadding

end OAI
