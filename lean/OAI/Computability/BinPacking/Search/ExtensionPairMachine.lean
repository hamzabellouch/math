import OAI.Computability.BinPacking.Reductions.BinaryPairMachine

namespace OAI

namespace BinPackingGap.ExtensionPairMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition

abbrev Tape := BinPackingCompleteness.BinaryPairMachine.Tape
abbrev Label := BinPackingCompleteness.BinaryPairMachine.Label
abbrev State := BinPackingCompleteness.BinaryPairMachine.State
abbrev Alphabet := BinPackingCompleteness.BinaryPairMachine.Alphabet
abbrev machine := BinPackingCompleteness.BinaryPairMachine.machine
abbrev tapes := BinPackingCompleteness.BinaryPairMachine.tapes
abbrev cfg (label : Option Label) (input counter saved : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  BinPackingCompleteness.BinaryPairMachine.cfg label input counter saved register

abbrev pairTrace := BinPackingCompleteness.BinaryPairMachine.pairTrace
abbrev pairInTime := BinPackingCompleteness.BinaryPairMachine.pairInTime
abbrev pairHaltInTime := BinPackingCompleteness.BinaryPairMachine.pairHaltInTime

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

@[instance_reducible] def alphabetFintype (k : machine.K) : Fintype (machine.Γ k) :=
  inferInstanceAs (Fintype Bool)

private theorem update_zero (input counter saved replacement : List Bool) :
    Function.update (tapes input counter saved) 0 replacement =
      tapes replacement counter saved := by
  funext k
  fin_cases k <;> simp [tapes, BinPackingCompleteness.BinaryPairMachine.tapes]

private theorem update_one (input counter saved replacement : List Bool) :
    Function.update (tapes input counter saved) 1 replacement =
      tapes input replacement saved := by
  funext k
  fin_cases k <;> simp [tapes, BinPackingCompleteness.BinaryPairMachine.tapes]

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem countStep_empty (counter saved : List Bool) (register : Option Bool) :
    machine.step (cfg (some 0) [] counter saved register) =
      some (cfg (some 4) [] counter saved) := by
  change some (TM2.stepAux (BinPackingCompleteness.BinaryPairMachine.program 0) _ _) = _
  simp [BinPackingCompleteness.BinaryPairMachine.program,
    BinPackingCompleteness.BinaryPairMachine.count,
    BinPackingCompleteness.BinaryPairMachine.stop, cfg,
    BinPackingCompleteness.BinaryPairMachine.cfg, TM2.stepAux, update_zero]
  rfl

theorem copyStep_missing (counter saved : List Bool) (register : Option Bool) :
    machine.step (cfg (some 1) [] (true :: counter) saved register) =
      some (cfg (some 4) [] counter saved) := by
  change some (TM2.stepAux (BinPackingCompleteness.BinaryPairMachine.program 1) _ _) = _
  simp [BinPackingCompleteness.BinaryPairMachine.program,
    BinPackingCompleteness.BinaryPairMachine.copy,
    BinPackingCompleteness.BinaryPairMachine.stop, cfg,
    BinPackingCompleteness.BinaryPairMachine.cfg, TM2.stepAux, update_zero, update_one]
  rfl

private theorem replicate_true_append_cons (n : Nat) (counter : List Bool) :
    List.replicate n true ++ true :: counter =
      true :: (List.replicate n true ++ counter) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [List.replicate_succ, List.cons_append] using
        congrArg (List.cons true) ih

theorem countRejectTrace (n : Nat) (counter saved : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some 0) (List.replicate n true) counter saved register)) =
      some (cfg (some 4) [] (List.replicate n true ++ counter) saved) := by
  induction n generalizing counter register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, advance_some,
        List.replicate_zero, List.nil_append] using countStep_empty counter saved register
  | succ n ih =>
      rw [List.replicate_succ, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [BinPackingCompleteness.BinaryPairMachine.countStep_true, ih]
      simp only [replicate_true_append_cons, List.cons_append]

theorem copyRejectTrace (input : List Bool) (extra : Nat) (saved : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some 1) input
        (List.replicate (input.length + extra + 1) true) saved register)) =
      some (cfg (some 4) [] (List.replicate extra true) (input.reverse ++ saved)) := by
  induction input generalizing saved register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        List.replicate_succ, List.reverse_nil, List.nil_append] using
        copyStep_missing (List.replicate extra true) saved register
  | cons bit input ih =>
      have hn : (bit :: input).length + extra + 1 =
          (input.length + extra + 1) + 1 := by simp only [List.length_cons]; omega
      rw [hn, List.replicate_succ, List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [BinPackingCompleteness.BinaryPairMachine.copyStep_cons, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

def noTerminatorInTime (n : Nat) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (List.replicate n true))
      (some (cfg (some 4) [] (List.replicate n true) [])) (n + 1) where
  steps := n + 1
  evals_in_steps := by
    change (advance machine.step)^[n + 1]
      (some (initList machine (List.replicate n true))) =
      some (cfg (some 4) [] (List.replicate n true) [])
    simpa only [BinPackingCompleteness.BinaryPairMachine.initList_eq, List.append_nil, cfg]
      using countRejectTrace n [] [] none
  steps_le_m := Nat.le_refl _

theorem truncatedTrace (n : Nat) (rest : List Bool) (short : rest.length < n) :
    (advance machine.step)^[n + rest.length + 2]
      (some (initList machine (encodeWord n ++ rest))) =
      some (cfg (some 4) [] (List.replicate (n - rest.length - 1) true) rest.reverse) := by
  have first := BinPackingCompleteness.BinaryPairMachine.countTrace n rest [] [] none
  simp only [List.append_nil] at first
  have second := copyRejectTrace rest (n - rest.length - 1) [] none
  have hn : rest.length + (n - rest.length - 1) + 1 = n := by omega
  rw [hn] at second
  simp only [List.append_nil] at second
  have full := joinTrace first second
  have htime : (n + 1) + (rest.length + 1) = n + rest.length + 2 := by omega
  simpa only [BinPackingCompleteness.BinaryPairMachine.initList_eq, htime] using full

def truncatedInTime (n : Nat) (rest : List Bool) (short : rest.length < n) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (encodeWord n ++ rest))
      (some (cfg (some 4) [] (List.replicate (n - rest.length - 1) true) rest.reverse))
      ((encodeWord n ++ rest).length + 1) where
  steps := n + rest.length + 2
  evals_in_steps := truncatedTrace n rest short
  steps_le_m := by simp only [List.length_append, encodeWord_length]; omega

theorem headerCases (bits : List Bool) :
    (∃ n, bits = List.replicate n true) ∨
      ∃ n rest, bits = encodeWord n ++ rest := by
  induction bits with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons bit bits ih =>
      cases bit with
      | false => exact Or.inr ⟨0, bits, rfl⟩
      | true =>
          rcases ih with ⟨n, hn⟩ | ⟨n, rest, hn⟩
          · exact Or.inl ⟨n + 1, by simp only [hn, List.replicate_succ]⟩
          · exact Or.inr ⟨n + 1, rest, by
              simpa only [encodeWord, List.replicate_succ, List.cons_append] using
                congrArg (List.cons true) hn⟩

private theorem decodePairAux_replicate (n read : Nat) :
    CookLevin.decodePairAux read (List.replicate n true) = none := by
  induction n generalizing read with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, CookLevin.decodePairAux] using ih (read + 1)

@[simp] theorem decodePair_replicate (n : Nat) :
    CookLevin.decodePair (List.replicate n true) = none :=
  decodePairAux_replicate n 0

theorem decodePair_frame (n : Nat) (rest : List Bool) :
    CookLevin.decodePair (encodeWord n ++ rest) =
      if n ≤ rest.length then some (rest.take n, rest.drop n) else none := by
  simpa only [CookLevin.decodePair, encodeWord, List.append_assoc,
    List.singleton_append, Nat.zero_add] using CookLevin.decodePairAux_frame 0 n rest

theorem decodePair_none_iff (bits : List Bool) :
    CookLevin.decodePair bits = none ↔
      (∃ n, bits = List.replicate n true) ∨
        ∃ n rest, bits = encodeWord n ++ rest ∧ rest.length < n := by
  constructor
  · intro rejected
    rcases headerCases bits with ⟨n, rfl⟩ | ⟨n, rest, rfl⟩
    · exact Or.inl ⟨n, rfl⟩
    · right
      refine ⟨n, rest, rfl, ?_⟩
      rw [decodePair_frame] at rejected
      by_cases h : n ≤ rest.length
      · simp only [ite_eq_left h, Option.some_ne_none] at rejected
      · omega
  · rintro (⟨n, rfl⟩ | ⟨n, rest, rfl, short⟩)
    · exact decodePair_replicate n
    · rw [decodePair_frame, ite_eq_right (by omega)]

theorem pairBits_of_decodePair (bits input witness : List Bool)
    (decoded : CookLevin.decodePair bits = some (input, witness)) :
    bits = CookLevin.pairBits (input, witness) := by
  rcases headerCases bits with ⟨n, rfl⟩ | ⟨n, rest, rfl⟩
  · rw [decodePair_replicate] at decoded
    contradiction
  · rw [decodePair_frame] at decoded
    by_cases hn : n ≤ rest.length
    · rw [ite_eq_left hn] at decoded
      have hp := Option.some.inj decoded
      have hx := congrArg Prod.fst hp
      have hy := congrArg Prod.snd hp
      dsimp only at hx hy
      have hlen : input.length = n := by
        rw [← hx]
        exact List.length_take_of_le hn
      rw [CookLevin.pairBits, hlen, ← hx, ← hy, List.append_assoc,
        List.take_append_drop]
    · rw [ite_eq_right hn] at decoded
      contradiction

theorem malformedTrace (bits : List Bool) (rejected : CookLevin.decodePair bits = none) :
    ∃ counter saved,
      counter.length + saved.length ≤ bits.length ∧
      (advance machine.step)^[bits.length + 1]
        (some (initList machine bits)) = some (cfg (some 4) [] counter saved) := by
  rcases (decodePair_none_iff bits).mp rejected with
    ⟨n, rfl⟩ | ⟨n, rest, rfl, short⟩
  · refine ⟨List.replicate n true, [], ?_, ?_⟩
    · simp only [List.length_replicate, List.length_nil, Nat.add_zero, le_refl]
    · simpa only [BinPackingCompleteness.BinaryPairMachine.initList_eq,
        List.length_replicate, List.append_nil] using countRejectTrace n [] [] none
  · refine ⟨List.replicate (n - rest.length - 1) true, rest.reverse, ?_, ?_⟩
    · simp only [List.length_replicate, List.length_reverse,
        List.length_append, encodeWord_length]
      omega
    · have ht : (encodeWord n ++ rest).length + 1 = n + rest.length + 2 := by
        simp only [List.length_append, encodeWord_length]
        omega
      rw [ht]
      exact truncatedTrace n rest short

def decodedInTime (bits input witness : List Bool)
    (decoded : CookLevin.decodePair bits = some (input, witness)) :
    StateTransition.EvalsToInTime machine.step (initList machine bits)
      (some (cfg (some 3) witness input [])) (3 * bits.length + 3) where
  steps := 3 * input.length + 3
  evals_in_steps := by
    rw [pairBits_of_decodePair bits input witness decoded]
    exact pairTrace input witness
  steps_le_m := by
    rw [pairBits_of_decodePair bits input witness decoded, CookLevin.pairBits_length]
    dsimp only
    omega

structure RejectedRun (bits : List Bool) where
  counter : List Bool
  saved : List Bool
  space_le : counter.length + saved.length ≤ bits.length
  execution : StateTransition.EvalsToInTime machine.step (initList machine bits)
    (some (cfg (some 4) [] counter saved)) (bits.length + 1)

noncomputable def malformedInTime (bits : List Bool)
    (rejected : CookLevin.decodePair bits = none) : RejectedRun bits := by
  let hc := malformedTrace bits rejected
  let counter := Classical.choose hc
  let hs := Classical.choose_spec hc
  let saved := Classical.choose hs
  let result := Classical.choose_spec hs
  exact {
    counter := counter
    saved := saved
    space_le := result.1
    execution := {
      steps := bits.length + 1
      evals_in_steps := result.2
      steps_le_m := Nat.le_refl _ } }

noncomputable def splitTime : Polynomial Nat := 3 * Polynomial.X + 3

theorem success_steps_le_splitTime (input witness : List Bool) :
    3 * input.length + 3 ≤ splitTime.eval (CookLevin.pairBits (input, witness)).length := by
  simp only [splitTime, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X, CookLevin.pairBits_length]
  omega

theorem rejected_steps_le_splitTime (bits : List Bool) :
    bits.length + 1 ≤ splitTime.eval bits.length := by
  simp only [splitTime, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

def ExitSpec (bits : List Bool) (finish : machine.Cfg) : Prop :=
  match CookLevin.decodePair bits with
  | some (input, witness) => finish = cfg (some 3) witness input []
  | none => ∃ counter saved,
      finish = cfg (some 4) [] counter saved ∧
        counter.length + saved.length ≤ bits.length

structure SplitRun (bits : List Bool) where
  finish : machine.Cfg
  execution : StateTransition.EvalsToInTime machine.step (initList machine bits)
    (some finish) (splitTime.eval bits.length)
  correct : ExitSpec bits finish

noncomputable def splitInTime (bits : List Bool) : SplitRun bits := by
  cases decoded : CookLevin.decodePair bits with
  | none =>
      let run := malformedInTime bits decoded
      refine ⟨cfg (some 4) [] run.counter run.saved, ?_, ?_⟩
      · exact {
          toEvalsTo := run.execution.toEvalsTo
          steps_le_m := Nat.le_trans run.execution.steps_le_m
            (rejected_steps_le_splitTime bits) }
      · simp only [ExitSpec, decoded]
        exact ⟨run.counter, run.saved, rfl, run.space_le⟩
  | some pair =>
      refine ⟨cfg (some 3) pair.2 pair.1 [], ?_, ?_⟩
      · simpa only [splitTime, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X] using
          decodedInTime bits pair.1 pair.2 decoded
      · simp only [ExitSpec, decoded]

end BinPackingGap.ExtensionPairMachine

end OAI
