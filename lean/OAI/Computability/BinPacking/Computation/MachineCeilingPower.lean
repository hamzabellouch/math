import OAI.Computability.BinPacking.Computation.PoweringMasterState
import OAI.Computability.BinPacking.PCP.PreprocessingRegularSoundness

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open BinPackingGames.Foundations.PCP

inductive Tape
  | input | work | power | saved | level | fuel | spare | product
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .work, .power, .saved, .level, .fuel,
  .spare, .product]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | init | fuelFirst | fuelSecond | guard | copyFirst | copySecond
  | compare | restore | decide | scale | transfer | cleanup
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.init, .fuelFirst, .fuelSecond, .guard,
  .copyFirst, .copySecond, .compare, .restore, .decide, .scale, .transfer, .cleanup]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def memory (input work power saved level fuel spare product : List Bool) : Tape → List Bool
  | .input => input
  | .work => work
  | .power => power
  | .saved => saved
  | .level => level
  | .fuel => fuel
  | .spare => spare
  | .product => product

@[simp] theorem update_work (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .work x = memory a x c d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_power (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .power x = memory a b x d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_saved (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .saved x = memory a b c x e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_level (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .level x = memory a b c d x f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_fuel (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .fuel x = memory a b c d e x g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_product (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .product x = memory a b c d e f g x := by
  funext k; cases k <;> rfl

variable {σ : Type}

def compareLoop : TM2.Stmt Alphabet Label (State σ) :=
  .pop .work (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.peek .power (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop .power (fun state _ => (state.1, none))
            (.push .saved (fun _ => true) (.goto fun _ => .compare)))
          (.load (fun state => ((state.1.1, true), none)) (.goto fun _ => .compare))))
      (.load (fun state => (state.1, none)) (.goto fun _ => .restore)))

def scaleLoop (g : Nat) : TM2.Stmt Alphabet Label (State σ) :=
  .pop .power (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (Reduction.MachineSubstitution.pushWord .product (List.replicate g true)
        (.goto fun _ => .scale))
      (.push .power (fun _ => false)
        (.push .level (fun _ => true)
          (.load (fun state => (state.1, none)) (.goto fun _ => .transfer)))))

def program (g : Nat) : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push .power (fun _ => false) (.push .power (fun _ => true)
      (.push .level (fun _ => false) (.goto fun _ => .fuelFirst)))
  | .fuelFirst => Reduction.MachineTransfer.loopAt
      .input .spare id false .fuelFirst (some .fuelSecond)
  | .fuelSecond => MachineCopy.forkLoop
      .spare .input .fuel false .fuelSecond (some .guard)
  | .guard => MachineUnaryCounter.guard .fuel .copyFirst .cleanup
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .input .spare id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      .spare .input .work false .copySecond (some .compare)
  | .compare => compareLoop
  | .restore => Reduction.MachineTransfer.loopAt
      .saved .power id false .restore (some .decide)
  | .decide => .branch (fun state => state.1.2)
      (.load (fun state => ((state.1.1, false), none)) (.goto fun _ => .scale))
      (.load (fun state => ((state.1.1, false), none)) (.goto fun _ => .cleanup))
  | .scale => scaleLoop g
  | .transfer => Reduction.MachineTransfer.loopAt
      .product .power id false .transfer (some .guard)
  | .cleanup => MachineDrain.drain .fuel .cleanup none

def overflow (flag : Bool) (x p : Nat) : Bool := flag || decide (p < x)

theorem compareStep_zero (g p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord 0) (encodeWord p) saved level fuel spare product⟩ =
      some ⟨some .restore, ((ambient, flag), none),
        memory input [] (encodeWord p) saved level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord]

theorem compareStep_succ_zero (g x : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord (x + 1)) (encodeWord 0) saved level fuel spare product⟩ =
      some ⟨some .compare, ((ambient, true), none),
        memory input (encodeWord x) (encodeWord 0) saved level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

theorem compareStep_succ_succ (g x p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord (x + 1)) (encodeWord (p + 1)) saved level fuel spare product⟩ =
      some ⟨some .compare, ((ambient, flag), none),
        memory input (encodeWord x) (encodeWord p) (true :: saved) level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

theorem compareTrace (g x p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step (program g)))^[x + 1]
      (some ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord x) (encodeWord p) saved level fuel spare product⟩) =
      some ⟨some .restore, ((ambient, overflow flag x p), none),
        memory input [] (encodeWord (p - x))
          (List.replicate (min x p) true ++ saved) level fuel spare product⟩ := by
  induction x generalizing p saved flag register with
  | zero =>
      simpa [overflow] using compareStep_zero g p input saved level fuel spare product ambient flag register
  | succ x ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step (program g)))^[x + 1]
        (TM2.step (program g) ⟨some .compare, ((ambient, flag), register),
          memory input (encodeWord (x + 1)) (encodeWord p) saved level fuel spare product⟩) = _
      cases p with
      | zero =>
          rw [compareStep_succ_zero]
          simpa [overflow] using ih 0 saved true none
      | succ p =>
          rw [compareStep_succ_succ]
          simpa [overflow, Nat.succ_min_succ, List.replicate_succ', List.append_assoc] using
            ih p (true :: saved) flag none

theorem replicate_encodeWord (a b : Nat) :
    List.replicate a true ++ encodeWord b = encodeWord (a + b) := by
  simp only [encodeWord, ← List.append_assoc, List.replicate_append_replicate]

theorem compareRestoredTrace (g k p : Nat) (level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[k + min k p + 2]
      (some ⟨some .compare, ((ambient, false), register),
        memory (encodeWord k) (encodeWord k) (encodeWord p) [] level fuel [] []⟩) =
      some ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] level fuel [] []⟩ := by
  have hc := compareTrace g k p (encodeWord k) [] level fuel [] [] ambient false register
  simp only [overflow, Bool.false_or, List.append_nil] at hc
  let mid := memory (encodeWord k) [] (encodeWord (p - k))
    (List.replicate (min k p) true) level fuel [] []
  have hr := Reduction.MachineTransfer.transferAt_fromTapes Tape.saved Tape.power (by decide)
    id false Label.restore (some Label.decide) (program g) rfl mid (ambient, decide (p < k)) none
  have hsum : min k p + (p - k) = p := by omega
  simp only [mid, memory, List.length_replicate, List.reverse_replicate, List.map_id,
    Reduction.MachineTransfer.tapesAt, update_saved, update_power] at hr
  rw [replicate_encodeWord, hsum] at hr
  rw [show k + min k p + 2 = (min k p + 1) + (k + 1) by omega,
    Function.iterate_add_apply, hc]
  exact hr

private theorem appendTrace {α : Type*} (f : α → α) {a b c : α} {s t : Nat}
    (hs : f^[s] a = b) (ht : f^[t] b = c) : f^[s + t] a = c := by
  rw [Nat.add_comm s t, Function.iterate_add_apply, hs, ht]

theorem scaleStep_succ (g p b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord (p + 1)) [] level fuel [] (List.replicate b true)⟩ =
      some ⟨some .scale, ((ambient, false), some true),
        memory input [] (encodeWord p) [] level fuel [] (List.replicate (g + b) true)⟩ := by
  change some (TM2.stepAux (scaleLoop g) _ _) = _
  simp [scaleLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ,
    Reduction.MachineSubstitution.stepAux_pushWord]

theorem scaleStep_zero (g b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord 0) [] level fuel [] (List.replicate b true)⟩ =
      some ⟨some .transfer, ((ambient, false), none),
        memory input [] (encodeWord 0) [] (true :: level) fuel [] (List.replicate b true)⟩ := by
  change some (TM2.stepAux (scaleLoop g) _ _) = _
  simp [scaleLoop, TM2.stepAux, memory, encodeWord]

theorem scaleScanTrace (g p b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[p + 1]
      (some ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord p) [] level fuel [] (List.replicate b true)⟩) =
      some ⟨some .transfer, ((ambient, false), none),
        memory input [] (encodeWord 0) [] (true :: level) fuel [] (List.replicate (g * p + b) true)⟩ := by
  induction p generalizing b register with
  | zero => simpa using scaleStep_zero g b input level fuel ambient register
  | succ p ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step (program g)))^[p + 1]
        (TM2.step (program g) ⟨some .scale, ((ambient, false), register),
          memory input [] (encodeWord (p + 1)) [] level fuel [] (List.replicate b true)⟩) = _
      rw [scaleStep_succ, ih]
      have h : g * p + (g + b) = g * (p + 1) + b := by rw [Nat.mul_succ]; omega
      rw [h]

theorem scaleTrace (g k p e : Nat) (fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[p + g * p + 2]
      (some ⟨some .scale, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) fuel [] []⟩) =
      some ⟨some .guard, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (p * g)) [] (encodeWord (e + 1)) fuel [] []⟩ := by
  have hs := scaleScanTrace g p 0 (encodeWord k) (encodeWord e) fuel ambient register
  simp only [List.replicate_zero, Nat.add_zero] at hs
  let mid := memory (encodeWord k) [] (encodeWord 0) [] (true :: encodeWord e) fuel []
    (List.replicate (g * p) true)
  have ht := Reduction.MachineTransfer.transferAt_fromTapes Tape.product Tape.power (by decide)
    id false Label.transfer (some Label.guard) (program g) rfl mid (ambient, false) none
  simp only [mid, memory, List.length_replicate, List.reverse_replicate, List.map_id,
    Reduction.MachineTransfer.tapesAt, update_product, update_power,
    replicate_encodeWord, Nat.add_zero] at ht
  have he : true :: encodeWord e = encodeWord (e + 1) := by simp [encodeWord, List.replicate_succ]
  rw [he, Nat.mul_comm g p] at ht
  rw [he, Nat.mul_comm g p] at hs
  have h := appendTrace (advance (TM2.step (program g))) hs ht
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using h

theorem cleanupTrace (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[f + 2]
      (some ⟨some .cleanup, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] []⟩ := by
  have h := MachineDrain.drainTrace Tape.fuel Label.cleanup none (program g) rfl
    (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    (encodeWord f) (ambient, false) register
  simpa only [encodeWord_length, update_fuel, Nat.add_assoc] using h

theorem guardStep_succ (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩ =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  have h := MachineUnaryCounter.guardStep_succ Tape.fuel Label.guard Label.copyFirst Label.cleanup
    (program g) rfl (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    f [] (ambient, false) register
  simpa only [MachineUnaryCounter.counterTapes, List.append_nil, update_fuel] using h

theorem guardStep_zero (g k p e : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ =
      some ⟨some .cleanup, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ := by
  have h := MachineUnaryCounter.guardStep_zero Tape.fuel Label.guard Label.copyFirst Label.cleanup
    (program g) rfl (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    [] (ambient, false) register
  simpa only [MachineUnaryCounter.counterTapes, List.append_nil, update_fuel] using h

theorem decideStep (g k p e f : Nat) (ambient : σ) :
    TM2.step (program g)
      ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  by_cases h : k ≤ p
  · have hn : ¬p < k := by omega
    simp [TM2.step, program, TM2.stepAux, h, hn]
  · have hn : p < k := by omega
    simp [TM2.step, program, TM2.stepAux, h, hn]

def prefixTime (k p : Nat) : Nat := (1 + 2 * (k + 2)) + (k + min k p + 2) + 1

theorem prefixTrace (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[prefixTime k p]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩) =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  have hg : (advance (TM2.step (program g)))^[1]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ :=
    guardStep_succ g k p e f ambient register
  have hc := MachineCopy.copyTrace Tape.input Tape.work Tape.spare
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.compare) (program g) rfl rfl
    (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] [])
    rfl (ambient, false) none
  simp only [memory, encodeWord_length, List.append_nil, update_work] at hc
  have hcmp := compareRestoredTrace g k p (encodeWord e) (encodeWord f) ambient none
  have hd : (advance (TM2.step (program g)))^[1]
      (some ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ :=
    decideStep g k p e f ambient
  exact appendTrace _ (appendTrace _ (appendTrace _ hg hc) hcmp) hd

def coreTime (g k : Nat) : Nat → Nat → Nat
  | 0, _ => 3
  | f + 1, p => prefixTime k p +
      if k ≤ p then f + 2 else (p + g * p + 2) + coreTime g k f (p * g)

theorem coreTrace (g k f e p : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[coreTime g k f p]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) []
          (encodeWord (PreprocessingLevels.levelLoop g k f e p).2) []
          (encodeWord (PreprocessingLevels.levelLoop g k f e p).1) [] [] []⟩ := by
  induction f generalizing e p register with
  | zero =>
      have hg : (advance (TM2.step (program g)))^[1]
          (some ⟨some .guard, ((ambient, false), register),
            memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩) =
          some ⟨some .cleanup, ((ambient, false), none),
            memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ :=
        guardStep_zero g k p e ambient register
      exact appendTrace _ hg (cleanupTrace g k p e 0 ambient none)
  | succ f ih =>
      have hpref := prefixTrace g k p e f ambient register
      by_cases h : k ≤ p
      · simp only [h, ite_true] at hpref
        have hrun := appendTrace _ hpref (cleanupTrace g k p e f ambient none)
        simpa only [coreTime, PreprocessingLevels.levelLoop, h, ite_true] using hrun
      · simp only [h, ite_false] at hpref
        have hscale := scaleTrace g k p e (encodeWord f) ambient none
        have hrun := appendTrace _ hpref (appendTrace _ hscale (ih (e + 1) (p * g) none))
        simpa only [coreTime, PreprocessingLevels.levelLoop, h, ite_false] using hrun

def roundBudget (g k : Nat) : Nat := (g + 8) * (k + 1) + 16

theorem prefixTime_le (k p : Nat) : prefixTime k p ≤ 4 * k + 8 := by
  have h := Nat.min_le_left k p
  unfold prefixTime
  omega

theorem prefixTime_le_roundBudget (g k p : Nat) : prefixTime k p ≤ roundBudget g k := by
  have h := prefixTime_le k p
  unfold roundBudget
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

theorem continuingTime_le (g k p : Nat) (h : p < k) :
    prefixTime k p + (p + g * p + 2) ≤ roundBudget g k := by
  have hprefix := prefixTime_le k p
  have hmul := Nat.mul_le_mul_left g h.le
  unfold roundBudget
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

theorem coreTime_le (g k f p : Nat) :
    coreTime g k f p ≤ (f + 1) * roundBudget g k := by
  have hB : 3 ≤ roundBudget g k := by unfold roundBudget; omega
  induction f generalizing p with
  | zero => simpa only [coreTime, Nat.zero_add, Nat.one_mul] using hB
  | succ f ih =>
      rw [coreTime]
      by_cases h : k ≤ p
      · rw [ite_eq_left h]
        have hp := prefixTime_le_roundBudget g k p
        have hm := Nat.mul_le_mul_left (f + 1) hB
        have hc : f + 2 ≤ (f + 1) * roundBudget g k := by omega
        calc
          prefixTime k p + (f + 2) ≤ roundBudget g k + (f + 1) * roundBudget g k :=
            Nat.add_le_add hp hc
          _ = (f + 1 + 1) * roundBudget g k := by ring
      · rw [ite_eq_right h]
        have hb := continuingTime_le g k p (by omega)
        have hr := ih (p * g)
        calc
          prefixTime k p + ((p + g * p + 2) + coreTime g k f (p * g)) =
              (prefixTime k p + (p + g * p + 2)) + coreTime g k f (p * g) := by omega
          _ ≤ roundBudget g k + (f + 1) * roundBudget g k := Nat.add_le_add hb hr
          _ = (f + 1 + 1) * roundBudget g k := by ring

theorem initStep (g k : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩ =
      some ⟨some .fuelFirst, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] []⟩ := by
  change some (TM2.stepAux (program g .init) _ _) = _
  simp [program, TM2.stepAux, memory, encodeWord]

def totalTime (g k : Nat) : Nat := 1 + 2 * (k + 2) + coreTime g k k 1

theorem searchTrace (g k : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[totalTime g k]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) []
          (encodeWord (PreprocessingLevels.levelLoop g k k 0 1).2) []
          (encodeWord (PreprocessingLevels.levelLoop g k k 0 1).1) [] [] []⟩ := by
  have hi : (advance (TM2.step (program g)))^[1]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨some .fuelFirst, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] []⟩ :=
    initStep g k ambient register
  have hc := MachineCopy.copyTrace Tape.input Tape.fuel Tape.spare
    (by decide) (by decide) (by decide) false Label.fuelFirst Label.fuelSecond
    (some Label.guard) (program g) rfl rfl
    (memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] [])
    rfl (ambient, false) register
  simp only [memory, encodeWord_length, List.append_nil, update_fuel] at hc
  exact appendTrace _ (appendTrace _ hi hc) (coreTrace g k k 0 1 ambient none)

def timeBound (g k : Nat) : Nat := (g + 8) * (k + 1) ^ 2 + 18 * (k + 1) + 3

theorem totalTime_le (g k : Nat) : totalTime g k ≤ timeBound g k := by
  have h := coreTime_le g k k 1
  calc
    totalTime g k ≤ 1 + 2 * (k + 2) + (k + 1) * roundBudget g k :=
      Nat.add_le_add_left h _
    _ = timeBound g k := by unfold roundBudget timeBound; ring

noncomputable def timePolynomial (g : Nat) : Polynomial Nat :=
  Polynomial.C (g + 8) * Polynomial.X ^ 2 + 18 * Polynomial.X + 3

theorem timePolynomial_encoding (g k : Nat) :
    (timePolynomial g).eval (encodeWord k).length = timeBound g k := by
  simp [timePolynomial, timeBound, encodeWord_length]

theorem paddingTrace (k : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program ExpanderFamily.growth)))^[totalTime ExpanderFamily.growth k]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (PreprocessingLevels.paddedSize k)) []
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] [] []⟩ := by
  exact searchTrace ExpanderFamily.growth k ambient register

def paddingInTime (k : Nat) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program ExpanderFamily.growth))
      ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩
      (some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (PreprocessingLevels.paddedSize k)) []
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] [] []⟩)
      ((timePolynomial ExpanderFamily.growth).eval (encodeWord k).length) where
  steps := totalTime ExpanderFamily.growth k
  evals_in_steps := paddingTrace k ambient register
  steps_le_m := by rw [timePolynomial_encoding]; exact totalTime_le _ _

theorem paddingOutput_bounds (k : Nat) :
    PreprocessingLevels.boundedLevel k ≤ k ∧
      k ≤ PreprocessingLevels.paddedSize k ∧
      PreprocessingLevels.paddedSize k ≤ ExpanderFamily.growth * (k + 1) := by
  refine ⟨PreprocessingLevels.boundedLevel_le_input k, PreprocessingLevels.le_paddedSize k, ?_⟩
  by_cases hk : k = 0
  · subst k
    simpa using ExpanderFamily.growth_gt_one.le
  · exact (PreprocessingLevels.paddedSize_bounds (Nat.pos_of_ne_zero hk)).2.trans
      (Nat.mul_le_mul_left ExpanderFamily.growth (Nat.le_succ k))

end BinPackingGames.Foundations.Complexity.MachineCeilingPower

end OAI
