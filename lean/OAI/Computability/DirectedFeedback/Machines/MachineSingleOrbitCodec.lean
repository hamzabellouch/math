import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineBinaryRenameMachine

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

namespace DFVSGames.Explicit.MachineSingleOrbitHeader

open Turing DFVSGames.Foundations.Complexity
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

theorem halfStep_first {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfFirst register (true :: i) c s r a o) =
      some (cfg .halfSecond (some true) i c s r a o) := by
  change some (TM2.stepAux (program q .halfFirst) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem halfStep_second {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfSecond register (true :: i) c s r a o) =
      some (cfg .halfFirst register i (true :: c) s r (true :: a) o) := by
  change some (TM2.stepAux (program q .halfSecond) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem halfStep_false {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfFirst register (false :: i) c s r a o) =
      some (cfg .alphabet none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q .halfFirst) _ _) = _
  simp [program, TM2.stepAux, cfg, initialState]

theorem halfTrace {q : Nat} (n : Nat) (suffix c s r a o : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[2 * n + 1]
      (some (cfg .halfFirst register (encodeWord (2 * n) ++ suffix) c s r a o)) =
      some (cfg .alphabet none suffix (List.replicate n true ++ c) s r
        ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing c a register with
  | zero =>
    simpa [encodeWord] using halfStep_false suffix c s r a o register
  | succ n ih =>
    have ht : 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 := by omega
    have hw : encodeWord (2 * (n + 1)) ++ suffix =
        true :: true :: (encodeWord (2 * n) ++ suffix) := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, ht, Function.iterate_succ_apply, advance_some, halfStep_first,
      Function.iterate_succ_apply, advance_some, halfStep_second, ih]
    congr 2
    · simp only [List.replicate_succ', List.append_assoc, List.singleton_append]
    · simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

theorem countStep_true {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .count register (true :: i) c s r a o) =
      some (cfg .count (some true) i c s (true :: r) (true :: a) o) := by
  change some (TM2.stepAux (program q .count) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem countStep_false {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .count register (false :: i) c s r a o) =
      some (cfg .guard none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q .count) _ _) = _
  simp [program, TM2.stepAux, cfg, initialState]

theorem countTrace {q : Nat} (n : Nat) (suffix c s r a o : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .count register (encodeWord n ++ suffix) c s r a o)) =
      some (cfg .guard none suffix c s (List.replicate n true ++ r)
        ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing r a register with
  | zero =>
    simpa [encodeWord] using countStep_false suffix c s r a o register
  | succ n ih =>
    have hw : encodeWord (n + 1) ++ suffix = true :: (encodeWord n ++ suffix) := by
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, Function.iterate_succ_apply, advance_some, countStep_true, ih]
    congr 2
    · simp only [List.replicate_succ', List.append_assoc, List.singleton_append]
    · simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

theorem initial_configuration (q : Nat) (input : List Bool) :
    initList (machine q) input = cfg .start none input [] [] [] [] [] := by
  have ht : (initList (machine q) input).stk = tapes input [] [] [] [] [] := by
    dsimp only [machine]
    funext t
    cases t <;> simp [initList, tapes]
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem initialStep (q : Nat) (input : List Bool) :
    TM2.step (program q) (initList (machine q) input) =
      some (cfg .halfFirst none input [false] [] [false] [] []) := by
  rw [initial_configuration]
  change some (TM2.stepAux (program q .start) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem headerTrace (q C m : Nat) (suffix : List Bool) :
    (advance (TM2.step (program q)))^[2 * C + q + m + 4]
      (some (initList (machine q)
        (encodeWord (2 * C) ++ encodeWord q ++ encodeWord m ++ suffix))) =
      some (cfg .guard none suffix (encodeWord C) [] (encodeWord m)
        (encodeWords [C, q, m]).reverse []) := by
  let input := encodeWord (2 * C) ++ encodeWord q ++ encodeWord m ++ suffix
  have hfirst :
      (advance (TM2.step (program q)))^[(2 * C + 1) + 1]
        (some (initList (machine q) input)) =
        some (cfg .alphabet none (encodeWord q ++ encodeWord m ++ suffix)
          (encodeWord C) [] [false] (encodeWord C).reverse []) := by
    rw [Function.iterate_add_apply _ (2 * C + 1) 1, Function.iterate_one]
    have first := congrArg ((advance (TM2.step (program q)))^[2 * C + 1])
      (initialStep q input)
    have rest := halfTrace (q := q) C (encodeWord q ++ encodeWord m ++ suffix)
      [false] [] [false] [] [] none
    refine first.trans ?_
    simpa only [input, encodeWord, List.append_nil, List.append_assoc] using rest
  have hsecond :
      (advance (TM2.step (program q)))^[(q + 1) + ((2 * C + 1) + 1)]
        (some (initList (machine q) input)) =
        some (cfg .count none (encodeWord m ++ suffix) (encodeWord C) [] [false]
          ((encodeWord q).reverse ++ (encodeWord C).reverse) []) := by
    rw [Function.iterate_add_apply _ (q + 1) ((2 * C + 1) + 1), hfirst]
    simpa only [List.append_assoc] using
      copyFieldTrace (q := q) .alphabet .count rfl q (encodeWord m ++ suffix)
        (encodeWord C) [] [false] (encodeWord C).reverse [] none
  have ht : 2 * C + q + m + 4 = (m + 1) + ((q + 1) + ((2 * C + 1) + 1)) := by omega
  change (advance (TM2.step (program q)))^[2 * C + q + m + 4]
    (some (initList (machine q) input)) = _
  rw [ht, Function.iterate_add_apply _ (m + 1) ((q + 1) + ((2 * C + 1) + 1)), hsecond]
  have hlast := countTrace (q := q) m suffix (encodeWord C) [] [false]
    ((encodeWord q).reverse ++ (encodeWord C).reverse) [] none
  simpa [encodeWord, encodeWords, List.reverse_append, List.append_assoc] using hlast

end DFVSGames.Explicit.MachineSingleOrbitHeader
end

section

namespace DFVSGames.Explicit.MachineSingleOrbitSubtract

open Turing DFVSGames.Foundations.Complexity DFVSGames.Reduction
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

theorem subtractStep_zero (q : Nat) (suffix saved remaining accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .subtract register suffix (encodeWord 0) saved remaining accumulator output) =
      some (cfg .restore none suffix (encodeWord 0) saved remaining accumulator output) := by
  change some (TM2.stepAux (program q .subtract) _ _) = _
  simp [program, TM2.stepAux, cfg, encodeWord, initialState]

theorem subtractStep_succ (q n : Nat)
    (suffix saved remaining accumulator output : List Bool) (register : Option Bool) :
    TM2.step (program q)
      (cfg .subtract register (List.replicate (n + 1) true ++ suffix)
        (encodeWord (n + 1)) saved remaining accumulator output) =
      some (cfg .subtract (some true) (List.replicate n true ++ suffix)
        (encodeWord n) (true :: saved) remaining accumulator output) := by
  change some (TM2.stepAux (program q .subtract) _ _) = _
  simp [program, TM2.stepAux, cfg, encodeWord, List.replicate_succ]

theorem subtractTrace (q n : Nat)
    (suffix saved remaining accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .subtract register (List.replicate n true ++ suffix)
        (encodeWord n) saved remaining accumulator output)) =
      some (cfg .restore none suffix (encodeWord 0)
        (List.replicate n true ++ saved) remaining accumulator output) := by
  induction n generalizing saved register with
  | zero =>
    simpa using subtractStep_zero q suffix saved remaining accumulator output register
  | succ n ih =>
    rw [Function.iterate_succ_apply, advance_some, subtractStep_succ, ih]
    congr 2
    simp [List.replicate_add, List.append_assoc]

theorem restore_tapes (suffix capacity saved remaining accumulator output newSaved newCapacity : List Bool) :
    MachineTransfer.tapesAt Tape.saved Tape.capacity
      (tapes suffix capacity saved remaining accumulator output) newSaved newCapacity =
      tapes suffix newCapacity newSaved remaining accumulator output := by
  simp [MachineTransfer.tapesAt]

theorem restoreTrace (q n : Nat) (suffix remaining accumulator output : List Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .restore none suffix (encodeWord 0) (List.replicate n true)
        remaining accumulator output)) =
      some (cfg .target none suffix (encodeWord n) [] remaining accumulator output) := by
  have h := MachineTransfer.transferAt_fromTapes (Γ := fun _ : Tape => Bool) (σ := Unit)
    Tape.saved Tape.capacity (by decide) id false (Label.restore : Label q) (some .target)
    (program q) rfl (tapes suffix (encodeWord 0) (List.replicate n true)
      remaining accumulator output) () none
  have next_eq : MachineTransfer.nextAt Tape.capacity (program q) =
      advance (TM2.step (program q)) := rfl
  rw [next_eq] at h
  simpa only [cfg, restore_tapes,
    tapes_saved, tapes_capacity, List.length_replicate,
    List.reverse_replicate, List.map_id, encodeWord, List.replicate_zero,
    List.nil_append] using h

theorem removeOffsetTrace (q C v : Nat) (suffix remaining accumulator output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[2 * (C + 1)]
      (some (cfg .subtract register (encodeWord (C + v) ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .target none (encodeWord v ++ suffix) (encodeWord C)
        [] remaining accumulator output) := by
  have hw : encodeWord (C + v) ++ suffix =
      List.replicate C true ++ (encodeWord v ++ suffix) := by
    simp only [encodeWord, List.replicate_add, List.append_assoc]
  rw [hw, show 2 * (C + 1) = (C + 1) + (C + 1) by omega,
    Function.iterate_add_apply, subtractTrace]
  simp only [List.append_nil]
  exact restoreTrace q C (encodeWord v ++ suffix) remaining accumulator output

end DFVSGames.Explicit.MachineSingleOrbitSubtract
end

section

namespace DFVSGames.Explicit.MachineSingleOrbitCodec

open DFVSGames.Foundations.Target DFVSGames.Foundations.Complexity

def doubleConstraint {n q : Nat} (c : Constraint n q) : Constraint (2 * n) q where
  source := ⟨c.source.val, by have := c.source.isLt; omega⟩
  target := ⟨n + c.target.val, by have := c.target.isLt; omega⟩
  permutation := c.permutation

def doubleInstance {q : Nat} (I : Instance q) : Instance q where
  vertices := 2 * I.vertices
  constraints := I.constraints.map doubleConstraint
  nonempty h := I.nonempty (List.map_eq_nil_iff.mp h)

def rowBits {n q : Nat} (c : Constraint n q) : List Bool :=
  encodeWords (constraintWords c)

def doubledRowBits {n q : Nat} (c : Constraint n q) : List Bool :=
  encodeWords (constraintWords (doubleConstraint c))

def rowsBits {n q : Nat} (cs : List (Constraint n q)) : List Bool :=
  encodeWords (cs.flatMap constraintWords)

def doubledRowsBits {n q : Nat} (cs : List (Constraint n q)) : List Bool :=
  encodeWords (cs.flatMap (fun c => constraintWords (doubleConstraint c)))

@[simp] theorem rowBits_eq {n q : Nat} (c : Constraint n q) :
    rowBits c = encodeWord c.source.val ++ encodeWord c.target.val ++
      encodeWords (tableWords c.permutation) := by
  simp [rowBits, constraintWords, encodeWords, List.append_assoc]

@[simp] theorem doubledRowBits_eq {n q : Nat} (c : Constraint n q) :
    doubledRowBits c = encodeWord c.source.val ++ encodeWord (n + c.target.val) ++
      encodeWords (tableWords c.permutation) := by
  simp [doubledRowBits, constraintWords, doubleConstraint, encodeWords, List.append_assoc]

@[simp] theorem rowsBits_nil {n q : Nat} : rowsBits ([] : List (Constraint n q)) = [] := rfl
@[simp] theorem doubledRowsBits_nil {n q : Nat} :
    doubledRowsBits ([] : List (Constraint n q)) = [] := rfl

@[simp] theorem rowsBits_cons {n q : Nat} (c : Constraint n q) (cs : List (Constraint n q)) :
    rowsBits (c :: cs) = rowBits c ++ rowsBits cs := by
  simp [rowsBits, rowBits]

@[simp] theorem doubledRowsBits_cons {n q : Nat} (c : Constraint n q)
    (cs : List (Constraint n q)) :
    doubledRowsBits (c :: cs) = doubledRowBits c ++ doubledRowsBits cs := by
  simp [doubledRowsBits, doubledRowBits]

theorem gameBits_eq {q : Nat} (I : Instance q) :
    gameBits I = encodeWord I.vertices ++ encodeWord q ++
      encodeWord I.constraints.length ++ rowsBits I.constraints := by
  simp [gameBits, gameWords, encodeWords, rowsBits, List.append_assoc]

theorem doubled_gameBits_eq {q : Nat} (I : Instance q) :
    gameBits (doubleInstance I) = encodeWord (2 * I.vertices) ++ encodeWord q ++
      encodeWord I.constraints.length ++ doubledRowsBits I.constraints := by
  simp [gameBits, gameWords, doubleInstance, encodeWords, doubledRowsBits,
    List.flatMap_map, List.append_assoc]

theorem input_length_eq {q : Nat} (I : Instance q) :
    (gameBits (doubleInstance I)).length =
      2 * I.vertices + q + I.constraints.length + 3 +
        (doubledRowsBits I.constraints).length := by
  rw [doubled_gameBits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem vertices_le_input_length {q : Nat} (I : Instance q) :
    I.vertices ≤ (gameBits (doubleInstance I)).length := by
  rw [input_length_eq]
  omega

theorem rows_le_input_length {q : Nat} (I : Instance q) :
    I.constraints.length ≤ (gameBits (doubleInstance I)).length := by
  rw [input_length_eq]
  omega

end DFVSGames.Explicit.MachineSingleOrbitCodec
end

section

namespace DFVSGames.Explicit.MachineSingleOrbitRows

open Turing DFVSGames.Foundations.Complexity DFVSGames.Foundations.Target
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams
open MachineSingleOrbitSubtract MachineSingleOrbitCodec

theorem joinTrace {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (h : f^[m] x = y) (h' : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, h, h']

def rowCost {C q : Nat} (c : Constraint C q) : Nat :=
  (doubledRowBits c).length + C + 3

theorem rowTrace {C q : Nat} (c : Constraint C q)
    (suffix remaining accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[rowCost c]
      (some (cfg .source register (doubledRowBits c ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .guard none suffix (encodeWord C) [] remaining
        ((rowBits c).reverse ++ accumulator) output) := by
  let table := encodeWords (tableWords c.permutation)
  let afterSource := (encodeWord c.source.val).reverse ++ accumulator
  let afterTarget := (encodeWord c.target.val).reverse ++ afterSource
  have hs := copyFieldTrace (q := q) .source .subtract rfl c.source.val
    (encodeWord (C + c.target.val) ++ table ++ suffix)
    (encodeWord C) [] remaining accumulator output register
  have hd := removeOffsetTrace q C c.target.val (table ++ suffix)
    remaining afterSource output none
  have ht := copyFieldTrace (q := q) .target (.table 0) rfl c.target.val
    (table ++ suffix) (encodeWord C) [] remaining afterSource output none
  have hp := tableTrace (q := q) 0 (tableWords c.permutation)
    (by simp) suffix (encodeWord C) [] remaining afterTarget output none
  have hs' : (advance (TM2.step (program q)))^[c.source.val + 1]
      (some (cfg .source register (doubledRowBits c ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .subtract none (encodeWord (C + c.target.val) ++ (table ++ suffix))
        (encodeWord C) [] remaining afterSource output) := by
    simpa only [doubledRowBits_eq, List.append_assoc, afterSource, table] using hs
  have hsd := joinTrace hs' hd
  have hsdt := joinTrace hsd ht
  have hall := joinTrace hsdt hp
  have hcost : (encodeWords (tableWords c.permutation)).length + 1 +
        (c.target.val + 1 + (2 * (C + 1) + (c.source.val + 1))) = rowCost c := by
    simp only [rowCost, doubledRowBits_eq, List.length_append, encodeWord_length]
    omega
  rw [hcost] at hall
  simpa only [rowBits_eq, List.reverse_append, List.append_assoc,
    afterTarget, afterSource, table] using hall

theorem guardStep_succ (q n : Nat) (input capacity saved accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .guard register input capacity saved (encodeWord (n + 1)) accumulator output) =
      some (cfg .source none input capacity saved (encodeWord n) accumulator output) := by
  change some (TM2.stepAux (program q .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux, cfg, encodeWord, List.replicate_succ]

theorem guardStep_zero (q : Nat) (input capacity saved accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .guard register input capacity saved (encodeWord 0) accumulator output) =
      some (cfg .finishStart none input capacity saved (encodeWord 0) accumulator output) := by
  change some (TM2.stepAux (program q .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux, cfg, encodeWord]

def rowsCost {C q : Nat} (cs : List (Constraint C q)) : Nat :=
  (doubledRowsBits cs).length + (C + 4) * cs.length + 1

theorem rowsCost_cons {C q : Nat} (c : Constraint C q) (cs : List (Constraint C q)) :
    rowsCost (c :: cs) = rowsCost cs + rowCost c + 1 := by
  simp only [rowsCost, rowCost, doubledRowsBits_cons, List.length_append,
    List.length_cons, Nat.mul_add, Nat.mul_one]
  omega

theorem rowsTrace {C q : Nat} (cs : List (Constraint C q))
    (suffix accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[rowsCost cs]
      (some (cfg .guard register (doubledRowsBits cs ++ suffix)
        (encodeWord C) [] (encodeWord cs.length) accumulator output)) =
      some (cfg .finishStart none suffix (encodeWord C) [] (encodeWord 0)
        ((rowsBits cs).reverse ++ accumulator) output) := by
  induction cs generalizing accumulator register with
  | nil =>
    simpa [rowsCost] using guardStep_zero q suffix (encodeWord C) [] accumulator output register
  | cons c cs ih =>
    have hg : (advance (TM2.step (program q)))^[1]
        (some (cfg .guard register (doubledRowsBits (c :: cs) ++ suffix)
          (encodeWord C) [] (encodeWord (c :: cs).length) accumulator output)) =
        some (cfg .source none (doubledRowBits c ++ (doubledRowsBits cs ++ suffix))
          (encodeWord C) [] (encodeWord cs.length) accumulator output) := by
      simpa only [Function.iterate_one, advance_some, List.length_cons,
        doubledRowsBits_cons, List.append_assoc] using
        guardStep_succ q cs.length (doubledRowsBits (c :: cs) ++ suffix)
          (encodeWord C) [] accumulator output register
    have hr := rowTrace c (doubledRowsBits cs ++ suffix) (encodeWord cs.length)
      accumulator output none
    have ht := ih ((rowBits c).reverse ++ accumulator) none
    have hall := joinTrace (joinTrace hg hr) ht
    have hcost : rowsCost cs + (rowCost c + 1) = rowsCost (c :: cs) := by
      rw [rowsCost_cons]
      omega
    rw [hcost] at hall
    simpa only [rowsBits_cons, List.reverse_append, List.append_assoc] using hall

end DFVSGames.Explicit.MachineSingleOrbitRows
end

section

namespace DFVSGames.Explicit.MachineSingleOrbitFinish

open Turing DFVSGames.Foundations.Complexity DFVSGames.Foundations.Hastad
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

noncomputable section

theorem haltList_eq (q : Nat) (bits : List Bool) : haltList (machine q) bits =
    ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  change (⟨none, initialState, (haltList (machine q) bits).stk⟩ : (machine q).Cfg) = _
  apply congrArg (fun base => (⟨none, initialState, base⟩ : (machine q).Cfg))
  dsimp only [machine]
  funext tape
  cases tape <;> simp [haltList, SourceRuntimeFinish.canonicalTapes] <;> rfl

def finishStartInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys Label.finish, initialState, base⟩) 1 where
  steps := 1
  evals_in_steps := by rfl
  steps_le_m := Nat.le_refl _

def timePolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q) clearKeys.length (prefixTime + 1)

def completePrefix (q : Nat) (input : List Bool) (prefixTime : Polynomial Nat)
    (base : Tape → List Bool)
    (execution : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨some .finishStart, initialState, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base .output = []) :
    TM2OutputsInTime (machine q) input (some (base .accumulator).reverse)
      ((timePolynomial q prefixTime).eval input.length) := by
  let bridge := finishStartInTime q base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨SourceRuntimeFinish.entry clearKeys Label.finish, initialState, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using
        joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys clearKeys_covers
    () Label.finish none (program q) (fun _ => rfl) base outputEmpty () none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (machine q) input (prefixTime + 1)
    prefixRun clearKeys Tape.accumulator Tape.output accumulator_not_mem_clearKeys
    output_not_mem_clearKeys clearKeys_covers base outputEmpty (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (machine q).step
    (initList (machine q) input)
    (some (haltList (machine q) (base .accumulator).reverse)) _
  rw [haltList_eq]
  exact run

end

end DFVSGames.Explicit.MachineSingleOrbitFinish
end

section

namespace DFVSGames.Explicit.MachineSingleOrbitRuntime

open Turing DFVSGames.Foundations.Complexity DFVSGames.Foundations.Target
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams
open MachineSingleOrbitCodec MachineSingleOrbitRows

noncomputable section

def finalTapes {q : Nat} (I : Instance q) : Tape → List Bool :=
  tapes [] (encodeWord I.vertices) [] (encodeWord 0) (gameBits I).reverse []

def prefixCost {q : Nat} (I : Instance q) : Nat :=
  (gameBits (doubleInstance I)).length + (I.vertices + 4) * I.constraints.length + 2

theorem prefixTrace {q : Nat} (I : Instance q) :
    (advance (TM2.step (program q)))^[prefixCost I]
      (some (initList (machine q) (gameBits (doubleInstance I)))) =
      some ⟨some .finishStart, initialState, finalTapes I⟩ := by
  have hh := MachineSingleOrbitHeader.headerTrace q I.vertices I.constraints.length
    (doubledRowsBits I.constraints)
  have hr := rowsTrace I.constraints []
    (encodeWords [I.vertices, q, I.constraints.length]).reverse [] none
  have hbits : gameBits I =
      encodeWords [I.vertices, q, I.constraints.length] ++ rowsBits I.constraints := by
    simpa only [encodeWords, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc] using gameBits_eq I
  have hr' : (advance (TM2.step (program q)))^[rowsCost I.constraints]
      (some (cfg .guard none (doubledRowsBits I.constraints) (encodeWord I.vertices) []
        (encodeWord I.constraints.length)
        (encodeWords [I.vertices, q, I.constraints.length]).reverse [])) =
      some ⟨some .finishStart, initialState, finalTapes I⟩ := by
    simpa only [List.append_nil, cfg, finalTapes, hbits, List.reverse_append, initialState]
      using hr
  have run := joinTrace hh hr'
  have hcost : rowsCost I.constraints +
      (2 * I.vertices + q + I.constraints.length + 4) = prefixCost I := by
    rw [prefixCost, input_length_eq]
    unfold rowsCost
    omega
  rw [hcost] at run
  simpa only [doubled_gameBits_eq] using run

def prefixPolynomial : Polynomial Nat :=
  Polynomial.X + (Polynomial.X + Polynomial.C 4) * Polynomial.X + Polynomial.C 2

theorem prefixCost_le {q : Nat} (I : Instance q) :
    prefixCost I ≤ prefixPolynomial.eval (gameBits (doubleInstance I)).length := by
  have hC := vertices_le_input_length I
  have hm := rows_le_input_length I
  have hp := Nat.mul_le_mul (Nat.add_le_add_right hC 4) hm
  simp only [prefixCost, prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

def prefixInTime {q : Nat} (I : Instance q) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (gameBits (doubleInstance I)))
      (some ⟨some .finishStart, initialState, finalTapes I⟩)
      (prefixPolynomial.eval (gameBits (doubleInstance I)).length) where
  steps := prefixCost I
  evals_in_steps := prefixTrace I
  steps_le_m := prefixCost_le I

def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineSingleOrbitFinish.timePolynomial q prefixPolynomial

def fullRunInTime {q : Nat} (I : Instance q) :
    TM2OutputsInTime (machine q) (gameBits (doubleInstance I))
      (some (gameBits I)) ((timePolynomial q).eval (gameBits (doubleInstance I)).length) := by
  let run := MachineSingleOrbitFinish.completePrefix q (gameBits (doubleInstance I))
    prefixPolynomial (finalTapes I) (prefixInTime I) rfl
  simpa only [finalTapes, tapes_accumulator, List.reverse_reverse, timePolynomial] using run

def computableInPolyTime (q : Nat) :
    TM2ComputableInPolyTime (fun I : Instance q => gameBits (doubleInstance I)) gameBits id where
  tm := machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q
  outputsFun I := by
    change TM2OutputsInTime (machine q) ((gameBits (doubleInstance I)).map id)
      (some ((gameBits I).map id))
      ((timePolynomial q).eval (gameBits (doubleInstance I)).length)
    dsimp only [machine]
    rw [List.map_id, List.map_id]
    exact fullRunInTime I

theorem workAlphabetFinite (q : Nat) (tape : (computableInPolyTime q).tm.K) :
    Finite ((computableInPolyTime q).tm.Γ tape) := by
  change Finite Bool
  infer_instance

end

end DFVSGames.Explicit.MachineSingleOrbitRuntime
end

section

namespace DFVSGames.Reduction.SourceEquationLookup

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition SourceMachine SourceEncoding
open SourceClauseLookup (discardFieldsTrace)

inductive Tape
  | source | index | work | scratch | field (slot : Fin 4)
  deriving DecidableEq, Fintype

inductive Label
  | copyOut | copyBack | headerFirst | headerSecond | guard
  | skip (slot : Fin 4)
  | read (slot : Fin 5 × Bool)
  deriving DecidableEq, Fintype

def fieldDestination (r : Nat) : Tape := .field ⟨min r 3, by omega⟩
def readStart (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 4 r, false)
def readLoop (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 4 r, true)
def skipLabel (r : Nat) : Label := if h : r < 4 then .skip ⟨r, h⟩ else .guard
def headerLabel (r : Nat) : Label :=
  if r = 0 then .headerFirst else if r = 1 then .headerSecond else .guard

variable {σ : Type}

def program : Label → TM2.Stmt (fun _ : Tape => Bool) Label (σ × Option Bool)
  | .copyOut => Reduction.MachineTransfer.loopAt .source .scratch id false
      .copyOut (some .copyBack)
  | .copyBack => MachineCopy.forkLoop .scratch .source .work false
      .copyBack (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .guard
  | .guard => MachineUnaryCounter.guard .index (skipLabel 0) (readStart 0)
  | .skip slot => MachineLookup.discard .work (.skip slot) (skipLabel (slot.val + 1))
  | .read slot =>
      if slot.1.val < 4 then
        if slot.2 then
          fieldLoop .work (fieldDestination slot.1.val) (.read (slot.1, true))
            (some (readStart (slot.1.val + 1)))
        else fieldStart (fieldDestination slot.1.val) (.read (slot.1, true))
      else SourceFieldArray.finish .work none

theorem atSkip (r : Nat) (hr : r < 4) :
    program (σ := σ) (skipLabel r) = MachineLookup.discard .work (skipLabel r) (skipLabel (r + 1)) := by
  simp [skipLabel, hr, program]

theorem atReadStart (r : Nat) (hr : r < 4) :
    program (σ := σ) (readStart r) = fieldStart (fieldDestination r) (readLoop r) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadLoop (r : Nat) (hr : r < 4) :
    program (σ := σ) (readLoop r) = fieldLoop .work (fieldDestination r) (readLoop r)
      (some (readStart (r + 1))) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadDone : program (σ := σ) (readStart 4) = SourceFieldArray.finish .work none := by
  simp [program, readStart, SourceFieldArray.boundedIndex]

theorem discardHeadersTrace (base : Tape → List Bool) (variableCount equations : Nat)
    (suffix : List Bool) (hinput : base .work = encodeWords [variableCount, equations] ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[variableCount + equations + 2]
      (some ⟨some .headerFirst, (ambient, none), base⟩) =
      some ⟨some .guard, (ambient, none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work headerLabel program base 0 [variableCount, equations]
    suffix (by
      intro r hr
      have he : r = 0 ∨ r = 1 := by simp at hr; omega
      rcases he with rfl | rfl <;> rfl) hinput ambient
  simpa [encodeWords_length, headerLabel] using ht

theorem discardFourTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 4) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords values).length]
      (some ⟨some (skipLabel 0), (ambient, none), base⟩) =
      some ⟨some .guard, (ambient, none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work skipLabel program base 0 values suffix
    (by intro r hr; simpa only [Nat.zero_add] using atSkip r (by omega)) hinput ambient
  simpa [hlen, skipLabel] using ht

theorem readFourTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 4) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords values).length + 5]
      (some ⟨some (readStart 0), (ambient, none), base⟩) =
      some ⟨none, (ambient, none),
        SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix⟩ := by
  have ht := SourceFieldArray.sequenceTrace .work fieldDestination readStart readLoop none
    program base 0 values suffix (by intro r hr; simp [fieldDestination])
    (by intro r hr; simpa only [Nat.zero_add] using atReadStart r (by omega))
    (by intro r hr; simpa only [Nat.zero_add] using atReadLoop r (by omega))
    (by simpa [hlen] using atReadDone) hinput ambient none
  have htime : values.sum + 2 * values.length + 1 = (encodeWords values).length + 5 := by
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

theorem skipEquationsTrace {n : Nat} (base : Tape → List Bool)
    (prior : List (CloneGap.Equation (Fin n))) (indexSuffix suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords (prior.flatMap equationWords)).length + prior.length + 1]
      (some ⟨some .guard, (ambient, register), scanTapes base prior.length indexSuffix
        (encodeWords (prior.flatMap equationWords) ++ suffix)⟩) =
      some ⟨some (readStart 0), (ambient, none), scanTapes base 0 indexSuffix suffix⟩ := by
  induction prior generalizing register with
  | nil =>
    simpa only [List.flatMap_nil, List.length_nil, encodeWords, List.nil_append,
      Nat.zero_add, Function.iterate_one, advance_some, scanTapes] using
      MachineUnaryCounter.guardStep_zero .index .guard (skipLabel 0) (readStart 0)
        program rfl (Function.update base .work suffix) indexSuffix ambient register
  | cons equation prior ih =>
    have hencoding : encodeWords ((equation :: prior).flatMap equationWords) ++ suffix =
        encodeWords (equationWords equation) ++ (encodeWords (prior.flatMap equationWords) ++ suffix) := by
      simp only [List.flatMap_cons, encodeWords_append, List.append_assoc]
    have htime : (encodeWords ((equation :: prior).flatMap equationWords)).length +
        (equation :: prior).length + 1 =
        ((encodeWords (prior.flatMap equationWords)).length + prior.length + 1 +
          (encodeWords (equationWords equation)).length) + 1 := by
      simp only [List.flatMap_cons, encodeWords_append, List.length_append, List.length_cons]
      omega
    rw [htime, Function.iterate_succ_apply]
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap equationWords)).length + prior.length + 1 +
        (encodeWords (equationWords equation)).length]
      (TM2.step program ⟨some .guard, (ambient, register),
        MachineUnaryCounter.counterTapes .index
          (Function.update base .work (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix))
          (prior.length + 1) indexSuffix⟩) = _
    rw [MachineUnaryCounter.guardStep_succ .index .guard (skipLabel 0) (readStart 0)
      program rfl]
    rw [Function.iterate_add_apply]
    have hd := discardFourTrace
      (scanTapes base prior.length indexSuffix
        (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix))
      (equationWords equation) (equationWords_length equation)
      (encodeWords (prior.flatMap equationWords) ++ suffix) (by
        rw [scanTapes_work, hencoding]) ambient
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap equationWords)).length + prior.length + 1]
      ((advance (TM2.step program))^[(encodeWords (equationWords equation)).length]
        (some ⟨some (skipLabel 0), (ambient, none), scanTapes base prior.length indexSuffix
          (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix)⟩)) = _
    rw [hd, update_scanTapes_work]
    exact ih none

theorem fieldDestination_eq (j : Fin 4) : fieldDestination j.val = .field j := by
  unfold fieldDestination
  congr 1
  apply Fin.ext
  exact Nat.min_eq_left (by omega)

theorem fieldDestination_injective_below (r s : Nat) (hr : r < 4) (hs : s < 4)
    (he : fieldDestination r = fieldDestination s) : r = s := by
  have hv := congrArg (fun t : Tape => match t with | .field j => j.val | _ => 4) he
  simpa [fieldDestination, Nat.min_eq_left (show r ≤ 3 by omega),
    Nat.min_eq_left (show s ≤ 3 by omega)] using hv

theorem readFour_output_field (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 4) (suffix : List Bool) (j : Fin 4) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix (.field j) =
      encodeWord (values[j.val]'(by omega)) ++ base (.field j) := by
  have ht := SourceFieldArray.sequenceTapes_selected .work fieldDestination base 0 values
    suffix j.val (by omega) (by intro r hr; simp [fieldDestination])
    (by
      intro r s hr hs he
      apply fieldDestination_injective_below r s (by omega) (by omega)
      simpa only [Nat.zero_add] using he)
  simpa only [Nat.zero_add, fieldDestination_eq] using ht

theorem readFour_output_work (base : Tape → List Bool) (values : List Nat)
    (_hlen : values.length = 4) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix .work = suffix := by
  apply SourceFieldArray.sequenceTapes_source _ _ _ _ _ _ _ hinput
  intro r hr
  simp [fieldDestination]

theorem readFour_output_frame (base : Tape → List Bool) (values : List Nat)
    (suffix : List Bool) (p : Tape) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 4, p ≠ .field j) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix p = base p := by
  apply SourceFieldArray.sequenceTapes_other _ _ _ hwork
  intro r hr
  exact hfield _

def outputTapes {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) : Tape → List Bool :=
  SourceFieldArray.sequenceTapes .work fieldDestination
    (scanTapes base 0 indexSuffix (encodeWords (equationWords equation) ++ suffix))
    0 (equationWords equation) suffix

def scanSteps {n : Nat} (variableCount declaredEquations : Nat)
    (prior : List (CloneGap.Equation (Fin n))) (equation : CloneGap.Equation (Fin n)) : Nat :=
  variableCount + declaredEquations + 2 +
    (encodeWords (prior.flatMap equationWords)).length + prior.length + 1 +
    (encodeWords (equationWords equation)).length + 5

theorem scanReadTrace {n : Nat} (base : Tape → List Bool) (variableCount declaredEquations : Nat)
    (prior : List (CloneGap.Equation (Fin n))) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[scanSteps variableCount declaredEquations prior equation]
      (some ⟨some .headerFirst, (ambient, none), scanTapes base prior.length indexSuffix
        (encodeWords [variableCount, declaredEquations] ++
          (encodeWords (prior.flatMap equationWords) ++
            (encodeWords (equationWords equation) ++ suffix)))⟩) =
      some ⟨none, (ambient, none), outputTapes base equation indexSuffix suffix⟩ := by
  have hh := discardHeadersTrace
    (scanTapes base prior.length indexSuffix
      (encodeWords [variableCount, declaredEquations] ++
        (encodeWords (prior.flatMap equationWords) ++ (encodeWords (equationWords equation) ++ suffix))))
    variableCount declaredEquations
    (encodeWords (prior.flatMap equationWords) ++ (encodeWords (equationWords equation) ++ suffix))
    (by simp) ambient
  have hs := skipEquationsTrace base prior indexSuffix (encodeWords (equationWords equation) ++ suffix) ambient none
  have hr := readFourTrace
    (scanTapes base 0 indexSuffix (encodeWords (equationWords equation) ++ suffix))
    (equationWords equation) (equationWords_length equation) suffix (by simp) ambient
  rw [show scanSteps variableCount declaredEquations prior equation =
      ((encodeWords (equationWords equation)).length + 5 +
        ((encodeWords (prior.flatMap equationWords)).length + prior.length + 1)) +
        (variableCount + declaredEquations + 2) by unfold scanSteps; omega]
  rw [Function.iterate_add_apply, hh, update_scanTapes_work,
    Function.iterate_add_apply, hs]
  exact hr

def lookupSteps {n : Nat} (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin n)))
    (equation : CloneGap.Equation (Fin n)) : Nat :=
  2 * ((inputBits F).length + 1) + scanSteps F.«variables» F.equations.length prior equation

theorem lookupWithSplitTrace (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin F.«variables»)))
    (equation : CloneGap.Equation (Fin F.«variables»)) (after : List (CloneGap.Equation (Fin F.«variables»)))
    (hsplit : F.equations = prior ++ equation :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[lookupSteps F prior equation]
      (some ⟨some .copyOut, (ambient, register), base⟩) =
      some ⟨none, (ambient, none),
        outputTapes base equation indexSuffix (encodeWords (after.flatMap equationWords))⟩ := by
  have hbits : inputBits F = encodeWords [F.«variables», F.equations.length] ++
      (encodeWords (prior.flatMap equationWords) ++
        (encodeWords (equationWords equation) ++ encodeWords (after.flatMap equationWords))) := by
    simp only [inputBits, inputWords, encodeWords_append]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append]
  have hc := MachineCopy.copyTrace .source .work .scratch (by decide) (by decide)
    (by decide) false .copyOut .copyBack (some .headerFirst) program rfl rfl
    base hscratch ambient register
  have htapes : Function.update base .work (base .source ++ base .work) =
      scanTapes base prior.length indexSuffix (inputBits F) := by
    funext p
    cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes, hsource, hindex, hwork]
  rw [htapes, hsource] at hc
  rw [lookupSteps, Nat.add_comm, Function.iterate_add_apply, hc, hbits]
  exact scanReadTrace base F.«variables» F.equations.length prior equation indexSuffix
    (encodeWords (after.flatMap equationWords)) ambient

theorem output_source {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix .source = base .source := by
  rw [outputTapes, readFour_output_frame _ _ _ .source (by decide) (by intro j; simp)]
  exact scanTapes_other _ _ _ _ _ (by decide) (by decide)

theorem output_index {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix .index = encodeWord 0 ++ indexSuffix := by
  rw [outputTapes, readFour_output_frame _ _ _ .index (by decide) (by intro j; simp),
    scanTapes_index]

theorem output_work {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix .work = suffix := by
  apply readFour_output_work _ _ (equationWords_length equation) _
  simp

theorem output_field {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) (j : Fin 4) :
    outputTapes base equation indexSuffix suffix (.field j) =
      encodeWord ((equationWords equation)[j.val]'(by simp)) ++ base (.field j) := by
  rw [outputTapes, readFour_output_field _ _ (equationWords_length equation)]
  rw [scanTapes_other _ _ _ _ (.field j) (by simp) (by simp)]

theorem output_first {n : Nat} (base : Tape → List Bool)
    (equation : CloneGap.Equation (Fin n)) (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix (.field 0) =
      encodeWord equation.first.val ++ base (.field 0) := by
  simpa [equationWords] using output_field base equation indexSuffix suffix (0 : Fin 4)

theorem output_second {n : Nat} (base : Tape → List Bool)
    (equation : CloneGap.Equation (Fin n)) (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix (.field 1) =
      encodeWord equation.second.val ++ base (.field 1) := by
  simpa [equationWords] using output_field base equation indexSuffix suffix (1 : Fin 4)

theorem output_third {n : Nat} (base : Tape → List Bool)
    (equation : CloneGap.Equation (Fin n)) (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix (.field 2) =
      encodeWord equation.third.val ++ base (.field 2) := by
  simpa [equationWords] using output_field base equation indexSuffix suffix (2 : Fin 4)

theorem output_rhs {n : Nat} (base : Tape → List Bool)
    (equation : CloneGap.Equation (Fin n)) (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix (.field 3) =
      encodeWord (if equation.rhs then 1 else 0) ++ base (.field 3) := by
  simpa [equationWords] using output_field base equation indexSuffix suffix (3 : Fin 4)

theorem output_frame {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) (p : Tape) (hindex : p ≠ .index) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 4, p ≠ .field j) :
    outputTapes base equation indexSuffix suffix p = base p := by
  rw [outputTapes, readFour_output_frame _ _ _ p hwork hfield]
  exact scanTapes_other _ _ _ _ p hindex hwork

theorem equationWords_four {n : Nat} (equation : CloneGap.Equation (Fin n)) :
    equationWords equation =
      [equation.first.val, equation.second.val, equation.third.val,
       if equation.rhs then 1 else 0] := rfl

def fieldWords (tapes : Tape → List Bool) : List (List Bool) :=
  [tapes (.field 0), tapes (.field 1), tapes (.field 2), tapes (.field 3)]

theorem output_fieldWords {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) (hempty : ∀ j : Fin 4, base (.field j) = []) :
    fieldWords (outputTapes base equation indexSuffix suffix) =
      (equationWords equation).map encodeWord := by
  simp [fieldWords, output_field, hempty, equationWords_four]

theorem lookupSteps_le_input (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin F.«variables»)))
    (equation : CloneGap.Equation (Fin F.«variables»)) (after : List (CloneGap.Equation (Fin F.«variables»)))
    (hsplit : F.equations = prior ++ equation :: after) :
    lookupSteps F prior equation ≤ 4 * (inputBits F).length + 8 := by
  have hlength : (inputBits F).length = F.«variables» + F.equations.length + 2 +
      (encodeWords (prior.flatMap equationWords)).length +
      (encodeWords (equationWords equation)).length +
      (encodeWords (after.flatMap equationWords)).length := by
    simp only [inputBits, inputWords, encodeWords_append, List.length_append,
      encodeWords, encodeWord_length, List.length_nil]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append, List.length_append]
    omega
  have hp : prior.length ≤ F.equations.length := by
    rw [hsplit, List.length_append, List.length_cons]
    omega
  unfold lookupSteps scanSteps
  omega

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 8

theorem timePolynomial_eval (L : Nat) : timePolynomial.eval L = 4 * L + 8 := by
  simp [timePolynomial]

def lookupWithSplitInTime (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin F.«variables»)))
    (equation : CloneGap.Equation (Fin F.«variables»)) (after : List (CloneGap.Equation (Fin F.«variables»)))
    (hsplit : F.equations = prior ++ equation :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, (ambient, register), base⟩
      (some ⟨none, (ambient, none),
        outputTapes base equation indexSuffix (encodeWords (after.flatMap equationWords))⟩)
      (timePolynomial.eval (inputBits F).length) where
  steps := lookupSteps F prior equation
  evals_in_steps := lookupWithSplitTrace F prior equation after hsplit base indexSuffix
    hsource hindex hwork hscratch ambient register
  steps_le_m := by
    rw [timePolynomial_eval]
    exact lookupSteps_le_input F prior equation after hsplit

def lookupInTime (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord i.val ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, (ambient, register), base⟩
      (some ⟨none, (ambient, none), outputTapes base F.equations[i.val] indexSuffix
        (encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords))⟩)
      (timePolynomial.eval (inputBits F).length) := by
  have hp : (F.equations.take i.val).length = i.val := by
    rw [List.length_take, Nat.min_eq_left i.isLt.le]
  have hs : F.equations = F.equations.take i.val ++ F.equations[i.val] :: F.equations.drop (i.val + 1) := by
    rw [List.getElem_cons_drop i.isLt, List.take_append_drop]
  apply lookupWithSplitInTime F (F.equations.take i.val) F.equations[i.val]
    (F.equations.drop (i.val + 1)) hs base indexSuffix hsource
    (by simpa only [hp] using hindex) hwork hscratch ambient register

def machine : FinTM2 where
  K := Tape
  k₀ := .source
  k₁ := .field 0
  Γ _ := Bool
  Λ := Label
  main := .copyOut
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program (σ := Unit)

def machineInTime (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord i.val ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some .copyOut, ((), register), base⟩
      (some ⟨none, ((), none), outputTapes base F.equations[i.val] indexSuffix
        (encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords))⟩)
      (timePolynomial.eval (inputBits F).length) := by
  exact lookupInTime F i base indexSuffix hsource hindex hwork hscratch () register

noncomputable def placedLookupInTime {Λ' : Type}
    (labels : Label → Λ') (exit : Option Λ')
    (target : Λ' → TM2.Stmt (fun _ : Tape => Bool) Λ' (σ × Option Bool))
    (atLabels : ∀ l, target (labels l) =
      MachineSubroutine.statement labels exit (program (σ := σ) l))
    (input : SourceEncoding.Input) (i : Fin input.equations.length)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits input)
    (hindex : base .index = encodeWord i.val ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels .copyOut), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), outputTapes base input.equations[i.val] indexSuffix
        (encodeWords ((input.equations.drop (i.val + 1)).flatMap equationWords))⟩)
      (timePolynomial.eval (inputBits input).length) :=
  MachineSubroutine.execution labels exit program target atLabels
    (lookupInTime input i base indexSuffix hsource hindex hwork hscratch ambient register)

noncomputable def embeddedLookupInTime {E Λextra τ : Type} [DecidableEq E]
    (continuation : Option (Label ⊕ Λextra)) (extraState : τ)
    (extraTapes : E → List Bool)
    (extra : Λextra → TM2.Stmt
      (MachineEmbedding.Alphabet (fun _ : Tape => Bool) (fun _ : E => Bool))
      (Label ⊕ Λextra) ((σ × Option Bool) × τ))
    (input : SourceEncoding.Input) (i : Fin input.equations.length)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits input)
    (hindex : base .index = encodeWord i.val ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime
      (TM2.step (MachineEmbedding.program continuation program extra))
      (MachineEmbedding.configuration continuation extraState extraTapes
        ⟨some .copyOut, (ambient, register), base⟩)
      (some (MachineEmbedding.configuration continuation extraState extraTapes
        ⟨none, (ambient, none), outputTapes base input.equations[i.val] indexSuffix
          (encodeWords ((input.equations.drop (i.val + 1)).flatMap equationWords))⟩))
      (timePolynomial.eval (inputBits input).length) :=
  MachineComposition.embeddedExecution continuation extraState extraTapes program extra
    (lookupInTime input i base indexSuffix hsource hindex hwork hscratch ambient register)

end DFVSGames.Reduction.SourceEquationLookup
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
