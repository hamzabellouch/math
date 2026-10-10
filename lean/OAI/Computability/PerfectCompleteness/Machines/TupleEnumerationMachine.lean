import OAI.Computability.PerfectCompleteness.Foundations.TupleIndexEmitterLemmas
import OAI.Computability.UniqueGames.Machines.MachineTupleOdometer

namespace OAI


namespace PerfectCompleteness.TupleEnumerationMachine

open Turing UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators


abbrev Tape (width : Nat) (Extra : Type) := TupleIndexEmitter.Tape width (Fin width ⊕ Extra)

inductive Label (width : Nat)
  | emit (label : TupleIndexEmitter.Label width)
  | check (coordinate : Fin width)
  | reset (coordinate : Fin width)
  | exit
  deriving DecidableEq, Fintype

variable {width : Nat} {Extra : Type} [DecidableEq Extra]

abbrev Alphabet (_ : Tape width Extra) := Bool
abbrev Register := Unit × Option Bool
abbrev Configuration := TM2.Cfg (Alphabet (width := width) (Extra := Extra))
  (Label width) Register

def checkAt (depth : Nat) : Label width :=
  if h : depth < width then .check ⟨depth, h⟩ else .exit

def currentAt (depth : Nat) : Tape width Extra :=
  if h : depth < width then .current ⟨depth, h⟩ else .scratch

def remainingAt (depth : Nat) : Tape width Extra :=
  if h : depth < width then .extra (.inl ⟨depth, h⟩) else .output

def body : Label width := .emit (TupleIndexEmitter.labelAt width)

def program : Label width →
    TM2.Stmt (Alphabet (width := width) (Extra := Extra)) (Label width) Register
  | .emit l => MachineSubroutine.statement Label.emit (some (checkAt 0)) (TupleIndexEmitter.program l)
  | .check i => MachineTupleOdometer.increment (.current i) (.extra (.inl i)) body (.reset i)
  | .reset i => MachineTupleOdometer.reset (.current i) (.extra (.inl i)) (.reset i) (checkAt (i.val + 1))
  | .exit => .halt

def resetAt (depth : Nat) : Label width :=
  if h : depth < width then .reset ⟨depth, h⟩ else .exit

def tapes (radix : Nat) (digits : Fin width → Nat) (output : List Bool)
    (extra : Extra → List Bool) : Tape width Extra → List Bool
  | .current i => encodeWord (digits i)
  | .scratch => []
  | .output => output
  | .extra (.inl i) => encodeWord (radix - 1 - digits i)
  | .extra (.inr x) => extra x

def configuration (label : Label width) (radix : Nat) (digits : Fin width → Nat)
    (output : List Bool) (extra : Extra → List Bool) :
    Configuration (width := width) (Extra := Extra) :=
  ⟨some label, ((), none), tapes radix digits output extra⟩

def setDigit (digits : Fin width → Nat) (depth value : Nat) : Fin width → Nat :=
  fun i => if i.val = depth then value else digits i

@[simp] theorem setDigit_self (digits : Fin width → Nat) (i : Fin width) (value : Nat) :
    setDigit digits i.val value i = value := by simp [setDigit]

theorem setDigit_zero (digits : Fin width → Nat) (depth : Nat)
    (hzero : ∀ i, i.val = depth → digits i = 0) : setDigit digits depth 0 = digits := by
  funext i
  by_cases hi : i.val = depth
  · simp [setDigit, hi, hzero i hi]
  · simp [setDigit, hi]

def prependBlocks (blocks : Nat → List Bool) : Nat → List Bool
  | 0 => []
  | count + 1 => blocks count ++ prependBlocks blocks count

theorem prependBlocks_eq (blocks : Nat → List Bool) (count : Nat) :
    prependBlocks blocks count = (List.range count).reverse.flatMap blocks := by
  induction count with
  | zero => simp [prependBlocks]
  | succ count ih => simp [prependBlocks, List.range_succ, ih]

def outputBlock (radix : Nat) : Nat → (Fin width → Nat) → List Bool
  | 0, digits => encodeWords (List.ofFn digits)
  | depth + 1, digits =>
      prependBlocks (fun value => outputBlock radix depth (setDigit digits depth value)) radix

@[simp] theorem outputBlock_zero (radix : Nat) (digits : Fin width → Nat) :
    outputBlock radix 0 digits = encodeWords (List.ofFn digits) := rfl

theorem outputBlock_succ (radix depth : Nat) (digits : Fin width → Nat) :
    outputBlock radix (depth + 1) digits = (List.range radix).reverse.flatMap
      (fun value => outputBlock radix depth (setDigit digits depth value)) := by
  exact prependBlocks_eq _ _

def fillDigits (digits : Fin width → Nat) {radix depth : Nat}
    (tuple : Fin depth → Fin radix) : Fin width → Nat :=
  fun i => if h : i.val < depth then (tuple ⟨i.val, h⟩).val else digits i

private theorem fillDigits_snoc (digits : Fin width → Nat) {radix depth : Nat}
    (tuple : Fin depth → Fin radix) (value : Fin radix) :
    fillDigits digits (Fin.snoc tuple value) =
      fillDigits (setDigit digits depth value.val) tuple := by
  funext i
  by_cases hi : i.val < depth
  · have hi' : i.val < depth + 1 := by omega
    simp [fillDigits, hi, hi', Fin.snoc]
  · by_cases heq : i.val = depth
    · simp [fillDigits, Fin.snoc, setDigit, heq]
    · have hi' : ¬i.val < depth + 1 := by omega
      simp [fillDigits, hi, hi', setDigit, heq]

private theorem range_eq_ofFn (radix : Nat) :
    List.range radix = (List.ofFn (fun i : Fin radix => i)).map Fin.val := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem outputBlock_eq_tupleOrder (radix depth : Nat) (digits : Fin width → Nat) :
    outputBlock radix depth digits =
      (MachineTupleOdometer.tupleOrder radix depth).reverse.flatMap
        (fun tuple => encodeWords (List.ofFn (fillDigits digits tuple))) := by
  induction depth generalizing digits with
  | zero =>
      rw [outputBlock_zero, MachineTupleOdometer.tupleOrder_dimension_zero]
      simp only [List.reverse_singleton, List.flatMap_singleton]
      apply congrArg encodeWords
      apply congrArg List.ofFn
      funext i
      simp [fillDigits]
  | succ depth ih =>
      rw [outputBlock_succ, range_eq_ofFn, ← List.map_reverse, List.flatMap_map,
        MachineTupleOdometer.tupleOrder_snoc, List.reverse_flatMap, List.flatMap_assoc]
      apply List.flatMap_congr
      intro value _
      change outputBlock radix depth (setDigit digits depth value.val) =
        ((MachineTupleOdometer.tupleOrder radix depth).map
          (fun tuple => Fin.snoc tuple value)).reverse.flatMap
            (fun tuple => encodeWords (List.ofFn (fillDigits digits tuple)))
      rw [← List.map_reverse, List.flatMap_map, ih]
      apply List.flatMap_congr
      intro tuple _
      change encodeWords (List.ofFn (fillDigits (setDigit digits depth value.val) tuple)) =
        encodeWords (List.ofFn (fillDigits digits (Fin.snoc tuple value)))
      rw [fillDigits_snoc]

@[simp] theorem fillDigits_all (digits : Fin width → Nat) {radix : Nat}
    (tuple : Fin width → Fin radix) : fillDigits digits tuple = fun i => (tuple i).val := by
  funext i
  simp [fillDigits, i.isLt]

theorem outputBlock_all (radix : Nat) :
    outputBlock radix width (fun _ : Fin width => 0) =
      (MachineTupleOdometer.tupleOrder radix width).reverse.flatMap
        (fun tuple => encodeWords (List.ofFn (fun i => (tuple i).val))) := by
  simpa only [fillDigits_all] using
    outputBlock_eq_tupleOrder radix width (fun _ : Fin width => 0)

private theorem tapes_output (radix : Nat) (digits : Fin width → Nat)
    (output bits : List Bool) (extra : Extra → List Bool) :
    TupleIndexEmitter.outputTapes (tapes radix digits output extra) bits =
      tapes radix digits (bits ++ output) extra := by
  funext tape
  cases tape with
  | current i => simp [TupleIndexEmitter.outputTapes, tapes]
  | scratch => simp [TupleIndexEmitter.outputTapes, tapes]
  | output => simp [TupleIndexEmitter.outputTapes, tapes]
  | extra x => cases x <;> simp [TupleIndexEmitter.outputTapes, tapes]

private theorem tapes_digit (radix depth remainder : Nat) (hdepth : depth < width)
    (hremainder : remainder ≤ radix - 1) (digits : Fin width → Nat)
    (output : List Bool) (extra : Extra → List Bool) :
    MachineTupleOdometer.digitTapes (currentAt depth) (remainingAt depth)
      (tapes radix digits output extra) (radix - 1 - remainder) remainder [] [] =
      tapes radix (setDigit digits depth (radix - 1 - remainder)) output extra := by
  have hsub : radix - 1 - (radix - 1 - remainder) = remainder := by omega
  funext tape
  cases tape with
  | current i =>
      by_cases hi : i.val = depth
      · have heq : i = (⟨depth, hdepth⟩ : Fin width) := Fin.ext hi
        subst i
        simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
          UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt, currentAt, remainingAt,
          hdepth, tapes, setDigit]
      · have heq : i ≠ (⟨depth, hdepth⟩ : Fin width) := fun h => hi (congrArg Fin.val h)
        simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
          UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt, currentAt, remainingAt,
          hdepth, tapes, setDigit, hi, heq]
  | scratch =>
      simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
        UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt, currentAt, remainingAt, hdepth, tapes]
  | output =>
      simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
        UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt, currentAt, remainingAt, hdepth, tapes]
  | extra x =>
      cases x with
      | inl i =>
          by_cases hi : i.val = depth
          · have heq : i = (⟨depth, hdepth⟩ : Fin width) := Fin.ext hi
            subst i
            simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
              UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt, currentAt, remainingAt,
              hdepth, tapes, setDigit, hsub]
          · have heq : i ≠ (⟨depth, hdepth⟩ : Fin width) := fun h => hi (congrArg Fin.val h)
            simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
              UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt, currentAt, remainingAt,
              hdepth, tapes, setDigit, hi, heq]
      | inr x =>
          simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
            UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt, currentAt, remainingAt, hdepth, tapes]

noncomputable def leafInTime (radix : Nat) (digits : Fin width → Nat)
    (output : List Bool) (extra : Extra → List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration body radix digits output extra)
      (some (configuration (checkAt 0) radix digits
        (outputBlock radix 0 digits ++ output) extra))
      ((∑ i, 2 * (digits i + 2)) + 1) := by
  have copied := TupleIndexEmitter.placedEmitInTime Label.emit (some (checkAt 0)) program
    (fun _ => rfl) digits (tapes radix digits output extra) (fun _ => rfl) rfl ()
  have returned : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.emit .done), ((), none),
        TupleIndexEmitter.outputTapes (tapes radix digits output extra) (encodeWords (List.ofFn digits))⟩
      (some ⟨some (checkAt 0), ((), none),
        TupleIndexEmitter.outputTapes (tapes radix digits output extra) (encodeWords (List.ofFn digits))⟩) 1 :=
    { steps := 1, evals_in_steps := rfl, steps_le_m := Nat.le_refl _ }
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copied returned
  simpa only [configuration, body, outputBlock_zero, tapes_output, Nat.add_comm] using joined

def leafBound (width radix : Nat) := 2 * width * (radix + 1) + 1

private theorem leafBudget_le (radix : Nat) (digits : Fin width → Nat)
    (bounded : ∀ i, digits i < radix) :
    (∑ i, 2 * (digits i + 2)) + 1 ≤ leafBound width radix := by
  have hsum : (∑ i, 2 * (digits i + 2)) ≤ ∑ _i : Fin width, 2 * (radix + 1) := by
    apply Finset.sum_le_sum
    intro i _
    exact Nat.mul_le_mul_left 2 (by have := bounded i; omega)
  simpa [leafBound, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    Nat.add_le_add_right hsum 1

theorem existsTree (radix : Nat) (positive : 0 < radix) (depth : Nat) (hdepth : depth ≤ width)
    (digits : Fin width → Nat) (zero : ∀ i, i.val < depth → digits i = 0)
    (bounded : ∀ i, digits i < radix) (output : List Bool) (extra : Extra → List Bool) :
    ∃ tree : MachineTupleOdometer.NestedCycle radix currentAt remainingAt body checkAt resetAt program depth
      (checkAt depth) (configuration body radix digits output extra)
      (configuration (checkAt depth) radix digits (outputBlock radix depth digits ++ output) extra),
      tree.LeafBound (leafBound width radix) := by
  induction depth generalizing digits output with
  | zero =>
      let run := leafInTime radix digits output extra
      refine ⟨.leaf (checkAt 0)
        (configuration body radix digits output extra)
        (configuration (checkAt 0) radix digits (outputBlock radix 0 digits ++ output) extra)
        run.steps rfl rfl run.evals_in_steps, ?_⟩
      erw [MachineTupleOdometer.NestedCycle.LeafBound]
      exact run.steps_le_m.trans (leafBudget_le radix digits bounded)
  | succ depth ih =>
      have hlt : depth < width := by omega
      let blocks := fun value => outputBlock radix depth (setDigit digits depth value)
      let emittedPrefix := prependBlocks blocks
      let schedule : MachineTupleOdometer.CycleSchedule (Tape width Extra) Unit :=
        {
          currentSuffix := []
          remainingSuffix := []
          ambient := fun _ => ()
          register := fun _ => none
          base := fun r => tapes radix digits (emittedPrefix (radix - r) ++ output) extra
        }
      have children : ∀ r : Fin radix,
          ∃ tree : MachineTupleOdometer.NestedCycle radix currentAt remainingAt body checkAt resetAt program depth
            (checkAt depth)
            (MachineTupleOdometer.bodyConfiguration (currentAt depth) (remainingAt depth) body (radix - 1) r.val
              schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base)
            (MachineTupleOdometer.checkConfiguration (currentAt depth) (remainingAt depth) (checkAt depth)
              (radix - 1) r.val schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.register schedule.base),
            tree.LeafBound (leafBound width radix) := by
        intro r
        have hr : r.val ≤ radix - 1 := by omega
        have hvalue : radix - 1 - r.val < radix := by omega
        have hbefore : radix - (r.val + 1) = radix - 1 - r.val := by omega
        have hafter : radix - r.val = (radix - 1 - r.val) + 1 := by omega
        have hz : ∀ i, i.val < depth → setDigit digits depth (radix - 1 - r.val) i = 0 := by
          intro i hi
          simp only [setDigit, ite_eq_right (by omega : i.val ≠ depth)]
          exact zero i (by omega)
        have hb : ∀ i, setDigit digits depth (radix - 1 - r.val) i < radix := by
          intro i
          by_cases hi : i.val = depth
          · simpa [setDigit, hi] using hvalue
          · simpa [setDigit, hi] using bounded i
        obtain ⟨tree, ht⟩ := ih (by omega) (setDigit digits depth (radix - 1 - r.val)) hz hb
          (emittedPrefix (radix - (r.val + 1)) ++ output)
        have hout : outputBlock radix depth (setDigit digits depth (radix - 1 - r.val)) ++
            (emittedPrefix (radix - (r.val + 1)) ++ output) = emittedPrefix (radix - r.val) ++ output := by
          rw [hbefore, hafter]
          simp only [emittedPrefix, prependBlocks, blocks, List.append_assoc]
        have childExists :
            ∃ child : MachineTupleOdometer.NestedCycle radix currentAt remainingAt body
              checkAt resetAt program depth (checkAt depth)
              (configuration body radix (setDigit digits depth (radix - 1 - r.val))
                (emittedPrefix (radix - (r.val + 1)) ++ output) extra)
              (configuration (checkAt depth) radix (setDigit digits depth (radix - 1 - r.val))
                (outputBlock radix depth (setDigit digits depth (radix - 1 - r.val)) ++
                  (emittedPrefix (radix - (r.val + 1)) ++ output)) extra),
              child.LeafBound (leafBound width radix) := ⟨tree, ht⟩
        rw [hout] at childExists
        have childStart :
            configuration body radix (setDigit digits depth (radix - 1 - r.val))
                (emittedPrefix (radix - (r.val + 1)) ++ output) extra =
              MachineTupleOdometer.bodyConfiguration (currentAt depth) (remainingAt depth) body
                (radix - 1) r.val schedule.currentSuffix schedule.remainingSuffix
                schedule.ambient schedule.base := by
          dsimp only [MachineTupleOdometer.bodyConfiguration, schedule, configuration]
          rw [tapes_digit radix depth r.val hlt hr]
        have childFinish :
            configuration (checkAt depth) radix (setDigit digits depth (radix - 1 - r.val))
                (emittedPrefix (radix - r.val) ++ output) extra =
              MachineTupleOdometer.checkConfiguration (currentAt depth) (remainingAt depth)
                (checkAt depth) (radix - 1) r.val schedule.currentSuffix schedule.remainingSuffix
                schedule.ambient schedule.register schedule.base := by
          dsimp only [MachineTupleOdometer.checkConfiguration, schedule, configuration]
          rw [tapes_digit radix depth r.val hlt hr]
        rw [childStart, childFinish] at childExists
        exact childExists
      let chosen := fun r => Classical.choose (children r)
      have chosenBound : ∀ r, (chosen r).LeafBound (leafBound width radix) :=
        fun r => Classical.choose_spec (children r)
      have distinct : currentAt (width := width) (Extra := Extra) depth ≠ remainingAt depth := by
        simp [currentAt, remainingAt, hlt]
      have atCheck : program (width := width) (Extra := Extra) (checkAt depth) =
          MachineTupleOdometer.increment (currentAt depth) (remainingAt depth) body (resetAt depth) := by
        simp [program, checkAt, currentAt, remainingAt, resetAt, hlt]
      have atReset : program (width := width) (Extra := Extra) (resetAt depth) =
          MachineTupleOdometer.reset (currentAt depth) (remainingAt depth) (resetAt depth) (checkAt (depth + 1)) := by
        simp [program, resetAt, currentAt, remainingAt, hlt]
      let tree := MachineTupleOdometer.NestedCycle.node depth (checkAt (depth + 1)) positive distinct
        atCheck atReset schedule chosen
      have treeBound : tree.LeafBound (leafBound width radix) := by
        simpa only [tree, MachineTupleOdometer.NestedCycle.LeafBound] using chosenBound
      have hz : setDigit digits depth 0 = digits :=
        setDigit_zero digits depth (fun i hi => zero i (by omega))
      have startTape : MachineTupleOdometer.digitTapes (currentAt depth) (remainingAt depth)
          (tapes radix digits (emittedPrefix (radix - ((radix - 1) + 1)) ++ output) extra)
          (radix - 1 - (radix - 1)) (radix - 1) [] [] = tapes radix digits output extra := by
        rw [tapes_digit radix depth (radix - 1) hlt (Nat.le_refl _)]
        simp only [Nat.sub_self, hz]
        have hn : radix - 1 + 1 = radix := by omega
        simp [hn, emittedPrefix, prependBlocks]
      have finishTape : MachineTupleOdometer.digitTapes (currentAt depth) (remainingAt depth)
          (tapes radix digits (emittedPrefix (radix - 0) ++ output) extra) 0 (radix - 1) [] [] =
          tapes radix digits (outputBlock radix (depth + 1) digits ++ output) extra := by
        have h := tapes_digit radix depth (radix - 1) hlt (Nat.le_refl _)
          digits (emittedPrefix radix ++ output) extra
        simpa only [Nat.sub_self, Nat.sub_zero, hz, outputBlock, emittedPrefix, blocks] using h
      have nodeExists :
          ∃ node : MachineTupleOdometer.NestedCycle radix currentAt remainingAt body
            checkAt resetAt program (depth + 1) (checkAt (depth + 1))
            (MachineTupleOdometer.bodyConfiguration (currentAt depth) (remainingAt depth) body
              (radix - 1) (radix - 1) schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.base)
            (MachineTupleOdometer.cycleExit (currentAt depth) (remainingAt depth)
              (checkAt (depth + 1)) (radix - 1) schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.base),
            node.LeafBound (leafBound width radix) := ⟨tree, treeBound⟩
      have nodeStart :
          MachineTupleOdometer.bodyConfiguration (currentAt depth) (remainingAt depth) body
              (radix - 1) (radix - 1) schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.base = configuration body radix digits output extra := by
        dsimp only [MachineTupleOdometer.bodyConfiguration, schedule, configuration]
        rw [startTape]
      have nodeFinish :
          MachineTupleOdometer.cycleExit (currentAt depth) (remainingAt depth)
              (checkAt (depth + 1)) (radix - 1) schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.base =
            configuration (checkAt (depth + 1)) radix digits
              (outputBlock radix (depth + 1) digits ++ output) extra := by
        dsimp only [MachineTupleOdometer.cycleExit, schedule, configuration]
        rw [finishTape]
      rw [nodeStart, nodeFinish] at nodeExists
      exact nodeExists

noncomputable def enumerateInTime (radix : Nat) (positive : 0 < radix)
    (output : List Bool) (extra : Extra → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (width := width) (Extra := Extra)))
      (configuration body radix (fun _ : Fin width => 0) output extra)
      (some (configuration .exit radix (fun _ : Fin width => 0)
        (outputBlock radix width (fun _ : Fin width => 0) ++ output) extra))
      ((leafBound width radix + 2 * width) * radix ^ width) := by
  let witness := existsTree radix positive width (Nat.le_refl _)
    (fun _ => 0) (fun _ _ => rfl) (fun _ => positive) output extra
  let tree := Classical.choose witness
  have bounded := Classical.choose_spec witness
  refine { steps := tree.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · change (MachineComposition.advance (TM2.step program))^[tree.steps]
      (some (configuration body radix (fun _ : Fin width => 0) output extra)) = _
    simpa only [checkAt, Nat.lt_irrefl, ↓reduceDIte] using tree.trace
  · exact tree.steps_le_power positive (leafBound width radix) bounded

def machine (width : Nat) (Extra : Type) [DecidableEq Extra] [Fintype Extra] : FinTM2 where
  K := Tape width Extra
  k₀ := .scratch
  k₁ := .output
  Γ _ := Bool
  Λ := Label width
  main := body
  σ := Register
  initialState := ((), none)
  m := program

end PerfectCompleteness.TupleEnumerationMachine

end OAI
