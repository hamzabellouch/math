import OAI.Computability.BinPacking.Computation.MachineUnaryLessAt

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineFixedDivMod

open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord statementPushBound_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) (d : Nat) := (σ × Fin d) × Option Bool

def residue (d : Nat) (positive : 0 < d) (n : Nat) : Fin d :=
  ⟨n % d, Nat.mod_lt n positive⟩

def nextResidue (d : Nat) (positive : 0 < d) (r : Fin d) : Fin d :=
  residue d positive (r.val + 1)

theorem nextResidue_residue (d : Nat) (positive : 0 < d) (n : Nat) :
    nextResidue d positive (residue d positive n) = residue d positive (n + 1) := by
  apply Fin.ext
  change (n % d + 1) % d = (n + 1) % d
  simp only [Nat.add_mod, Nat.mod_mod]

def scanLoop (d : Nat) (positive : 0 < d) (source quotient : K)
    (scanLabel : Λ) (emitterLabel : Fin d → Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ d) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.branch (fun state => decide ((nextResidue d positive state.1.2).val = 0))
        (.push quotient (fun _ => true)
          (.load (fun state => ((state.1.1, nextResidue d positive state.1.2), state.2))
            (.goto fun _ => scanLabel)))
        (.load (fun state => ((state.1.1, nextResidue d positive state.1.2), state.2))
          (.goto fun _ => scanLabel)))
      (.push source (fun _ => false) (.goto fun state => emitterLabel state.1.2)))

def emitter (d : Nat) (positive : 0 < d) (remainder : K) (exit : Option Λ)
    (r : Fin d) : TM2.Stmt (Alphabet (K := K)) Λ (State σ d) :=
  pushWord remainder (List.replicate r.val true)
    (.load (fun state => ((state.1.1, residue d positive 0), none))
      (Reduction.MachineTransfer.exitAt remainder exit))

omit [DecidableEq K] in
theorem scanPushBound (d : Nat) (positive : 0 < d) (source quotient : K)
    (scanLabel : Λ) (emitterLabel : Fin d → Λ) :
    Runtime.statementPushBound (scanLoop (σ := σ) d positive source quotient scanLabel
      emitterLabel) = 1 := rfl

omit [DecidableEq K] in
theorem emitterPushBound (d : Nat) (positive : 0 < d) (remainder : K)
    (exit : Option Λ) (r : Fin d) :
    Runtime.statementPushBound (emitter (σ := σ) d positive remainder exit r) = r.val := by
  cases exit <;>
    simp [emitter, statementPushBound_pushWord, Runtime.statementPushBound,
      Reduction.MachineTransfer.exitAt]

abbrev tapes (source quotient remainder : K) (base : K → List Bool)
    (input quotientWord remainderWord : List Bool) : K → List Bool :=
  MachineCopy.forkTapes source quotient remainder base input quotientWord remainderWord

def unaryTapes (source quotient remainder : K) (base : K → List Bool)
    (n q r : Nat) (sourceSuffix quotientSuffix remainderSuffix : List Bool) : K → List Bool :=
  tapes source quotient remainder base (encodeWord n ++ sourceSuffix)
    (encodeWord q ++ quotientSuffix) (encodeWord r ++ remainderSuffix)

@[simp] theorem unaryTapes_source (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (base : K → List Bool) (n q r : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    unaryTapes source quotient remainder base n q r sourceSuffix quotientSuffix
      remainderSuffix source = encodeWord n ++ sourceSuffix := by
  simp [unaryTapes, sourceQuotient, sourceRemainder]

@[simp] theorem unaryTapes_quotient (source quotient remainder : K)
    (quotientRemainder : quotient ≠ remainder) (base : K → List Bool) (n q r : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    unaryTapes source quotient remainder base n q r sourceSuffix quotientSuffix
      remainderSuffix quotient = encodeWord q ++ quotientSuffix := by
  simp [unaryTapes, quotientRemainder]

@[simp] theorem unaryTapes_remainder (source quotient remainder : K)
    (base : K → List Bool) (n q r : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    unaryTapes source quotient remainder base n q r sourceSuffix quotientSuffix
      remainderSuffix remainder = encodeWord r ++ remainderSuffix := by
  simp [unaryTapes]

theorem unaryTapes_other (source quotient remainder other : K)
    (notSource : other ≠ source) (notQuotient : other ≠ quotient)
    (notRemainder : other ≠ remainder) (base : K → List Bool) (n q r : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    unaryTapes source quotient remainder base n q r sourceSuffix quotientSuffix
      remainderSuffix other = base other := by
  simp [unaryTapes, tapes, MachineCopy.forkTapes, notSource, notQuotient, notRemainder]

private theorem update_source (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (base : K → List Bool)
    (input quotientWord remainderWord replacement : List Bool) :
    Function.update (tapes source quotient remainder base input quotientWord remainderWord)
      source replacement = tapes source quotient remainder base replacement quotientWord remainderWord := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [tapes, MachineCopy.forkTapes, sourceQuotient, sourceRemainder]
  · by_cases hq : k = quotient
    · subst k
      simp [tapes, MachineCopy.forkTapes, Ne.symm sourceQuotient, quotientRemainder]
    · by_cases hr : k = remainder
      · subst k
        simp [tapes, MachineCopy.forkTapes, Ne.symm sourceRemainder]
      · simp [tapes, MachineCopy.forkTapes, hs, hq, hr]

private theorem update_quotient (source quotient remainder : K)
    (quotientRemainder : quotient ≠ remainder) (base : K → List Bool)
    (input quotientWord remainderWord replacement : List Bool) :
    Function.update (tapes source quotient remainder base input quotientWord remainderWord)
      quotient replacement = tapes source quotient remainder base input replacement remainderWord := by
  funext k
  by_cases hq : k = quotient
  · subst k
    simp [tapes, MachineCopy.forkTapes, quotientRemainder]
  · by_cases hr : k = remainder
    · subst k
      simp [tapes, MachineCopy.forkTapes, Ne.symm quotientRemainder]
    · simp [tapes, MachineCopy.forkTapes, hq, hr]

private theorem update_remainder (source quotient remainder : K) (base : K → List Bool)
    (input quotientWord remainderWord replacement : List Bool) :
    Function.update (tapes source quotient remainder base input quotientWord remainderWord)
      remainder replacement = tapes source quotient remainder base input quotientWord replacement := by
  simp [tapes, MachineCopy.forkTapes]

theorem scanAux_true (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (base : K → List Bool) (input quotientWord remainderWord : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.stepAux (scanLoop d positive source quotient scanLabel emitterLabel)
      ((ambient, r), register)
      (tapes source quotient remainder base (true :: input) quotientWord remainderWord) =
      ⟨some scanLabel, ((ambient, nextResidue d positive r), some true),
        tapes source quotient remainder base input
          (if (nextResidue d positive r).val = 0 then true :: quotientWord else quotientWord)
          remainderWord⟩ := by
  by_cases hcarry : (nextResidue d positive r).val = 0 <;>
    simp [scanLoop, TM2.stepAux, sourceQuotient, sourceRemainder, quotientRemainder,
      update_source, update_quotient, hcarry]

theorem scanAux_false (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (base : K → List Bool) (input quotientWord remainderWord : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.stepAux (scanLoop d positive source quotient scanLabel emitterLabel)
      ((ambient, r), register)
      (tapes source quotient remainder base (false :: input) quotientWord remainderWord) =
      ⟨some (emitterLabel r), ((ambient, r), some false),
        tapes source quotient remainder base (false :: input) quotientWord remainderWord⟩ := by
  simp [scanLoop, TM2.stepAux, sourceQuotient, sourceRemainder, quotientRemainder,
    update_source]

theorem scanStep_succ (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (base : K → List Bool) (n k : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
      unaryTapes source quotient remainder base (n + 1) (k / d) 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨some scanLabel, ((ambient, residue d positive (k + 1)), some true),
        unaryTapes source quotient remainder base n ((k + 1) / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, residue d positive k), register)
    (unaryTapes source quotient remainder base (n + 1) (k / d) 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atScan]
  simp only [unaryTapes, encodeWord, List.replicate_succ, List.cons_append]
  rw [scanAux_true d positive source quotient remainder sourceQuotient sourceRemainder
    quotientRemainder, nextResidue_residue]
  by_cases hmod : (k + 1) % d = 0
  · rw [Nat.succ_div_of_mod_eq_zero hmod]
    simp [residue, hmod, List.replicate_succ]
  · rw [Nat.succ_div_of_mod_ne_zero hmod]
    simp [residue, hmod]

theorem scanStep_zero (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (base : K → List Bool) (q : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, r), register),
      unaryTapes source quotient remainder base 0 q 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨some (emitterLabel r), ((ambient, r), some false),
        unaryTapes source quotient remainder base 0 q 0
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, r), register)
    (unaryTapes source quotient remainder base 0 q 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atScan]
  simp only [unaryTapes, encodeWord, List.replicate_zero, List.nil_append,
    List.singleton_append]
  rw [scanAux_false d positive source quotient remainder sourceQuotient sourceRemainder
    quotientRemainder]

theorem emitterStep (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (emitterLabel : Fin d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atEmitter : ∀ r, program (emitterLabel r) = emitter d positive remainder exit r)
    (base : K → List Bool) (n q : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.step program ⟨some (emitterLabel r), ((ambient, r), register),
      unaryTapes source quotient remainder base n q 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨exit, ((ambient, residue d positive 0), none),
        unaryTapes source quotient remainder base n q r.val
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program (emitterLabel r)) ((ambient, r), register)
    (unaryTapes source quotient remainder base n q 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atEmitter]
  unfold emitter
  rw [stepAux_pushWord]
  simp only [unaryTapes, MachineCopy.forkTapes_right, List.reverse_replicate]
  rw [update_remainder]
  cases exit <;>
    simp [TM2.stepAux, Reduction.MachineTransfer.exitAt, encodeWord, List.append_assoc]

theorem trace_fromCount (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) = emitter d positive remainder exit r)
    (base : K → List Bool) (n k : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base n (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨exit, ((ambient, residue d positive 0), none),
        unaryTapes source quotient remainder base 0 ((k + n) / d) ((k + n) % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  induction n generalizing k register with
  | zero =>
    change (TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
      unaryTapes source quotient remainder base 0 (k / d) 0
        sourceSuffix quotientSuffix remainderSuffix⟩).bind (TM2.step program) = _
    rw [scanStep_zero d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel program atScan, Option.bind_some]
    simpa only [residue, Nat.add_zero] using
      emitterStep d positive source quotient remainder emitterLabel exit program atEmitter
        base 0 (k / d) sourceSuffix quotientSuffix remainderSuffix ambient
        (residue d positive k) (some false)
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 2]
      (TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base (n + 1) (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) = _
    rw [scanStep_succ d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel program atScan]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1) (some true)

theorem divModTrace (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) = emitter d positive remainder exit r)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive 0), register),
        unaryTapes source quotient remainder base n 0 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨exit, ((ambient, residue d positive 0), none),
        unaryTapes source quotient remainder base 0 (n / d) (n % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  simpa only [Nat.zero_add, Nat.zero_div] using
    trace_fromCount d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel exit program atScan atEmitter base n 0
      sourceSuffix quotientSuffix remainderSuffix ambient register

theorem divModFromTapes (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) = emitter d positive remainder exit r)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base source = encodeWord n ++ sourceSuffix)
    (quotientInput : base quotient = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base remainder = encodeWord 0 ++ remainderSuffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive 0), register), base⟩) =
      some ⟨exit, ((ambient, residue d positive 0), none),
        unaryTapes source quotient remainder base 0 (n / d) (n % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hbase : unaryTapes source quotient remainder base n 0 0 sourceSuffix quotientSuffix
      remainderSuffix = base := by
    simp only [unaryTapes, ← sourceInput, ← quotientInput, ← remainderInput,
      MachineCopy.forkTapes_self]
  have h := divModTrace d positive source quotient remainder sourceQuotient sourceRemainder
    quotientRemainder scanLabel emitterLabel exit program atScan atEmitter base n
    sourceSuffix quotientSuffix remainderSuffix ambient register
  rw [hbase] at h
  exact h

def divModInTime (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) = emitter d positive remainder exit r)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base source = encodeWord n ++ sourceSuffix)
    (quotientInput : base quotient = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base remainder = encodeWord 0 ++ remainderSuffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some scanLabel, ((ambient, residue d positive 0), register), base⟩
      (some ⟨exit, ((ambient, residue d positive 0), none),
        unaryTapes source quotient remainder base 0 (n / d) (n % d)
          sourceSuffix quotientSuffix remainderSuffix⟩) (n + 2) where
  steps := n + 2
  evals_in_steps := divModFromTapes d positive source quotient remainder sourceQuotient
    sourceRemainder quotientRemainder scanLabel emitterLabel exit program atScan atEmitter
    base n sourceSuffix quotientSuffix remainderSuffix sourceInput quotientInput remainderInput
    ambient register
  steps_le_m := Nat.le_refl _

theorem scanTrace_fromCount (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (base : K → List Bool) (n k : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base n (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨some (emitterLabel (residue d positive (k + n))),
        ((ambient, residue d positive (k + n)), some false),
        unaryTapes source quotient remainder base 0 ((k + n) / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  induction n generalizing k register with
  | zero =>
    simpa only [Nat.zero_add, Nat.add_zero, Function.iterate_one,
      MachineComposition.advance_some] using
      scanStep_zero d positive source quotient remainder sourceQuotient sourceRemainder
        quotientRemainder scanLabel emitterLabel program atScan base (k / d)
        sourceSuffix quotientSuffix remainderSuffix ambient (residue d positive k) register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base (n + 1) (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) = _
    rw [scanStep_succ d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel program atScan]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1) (some true)

def emitterWithFinish [Fintype σ] (d : Nat) (positive : 0 < d) (remainder : K)
    (exit : Option Λ) (finish : σ → Fin d → σ) (r : Fin d) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ d) :=
  pushWord remainder (List.replicate r.val true)
    (.load (fun state => ((finish state.1.1 r, residue d positive 0), none))
      (Reduction.MachineTransfer.exitAt remainder exit))

omit [DecidableEq K] in
theorem emitterWithFinishPushBound [Fintype σ] (d : Nat) (positive : 0 < d)
    (remainder : K) (exit : Option Λ) (finish : σ → Fin d → σ) (r : Fin d) :
    Runtime.statementPushBound (emitterWithFinish d positive remainder exit finish r) =
      r.val := by
  cases exit <;>
    simp [emitterWithFinish, statementPushBound_pushWord, Runtime.statementPushBound,
      Reduction.MachineTransfer.exitAt]

theorem emitterWithFinishStep [Fintype σ] (d : Nat) (positive : 0 < d)
    (source quotient remainder : K) (emitterLabel : Fin d → Λ) (exit : Option Λ)
    (finish : σ → Fin d → σ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atEmitter : ∀ r, program (emitterLabel r) =
      emitterWithFinish d positive remainder exit finish r)
    (base : K → List Bool) (n q : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.step program ⟨some (emitterLabel r), ((ambient, r), register),
      unaryTapes source quotient remainder base n q 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨exit, ((finish ambient r, residue d positive 0), none),
        unaryTapes source quotient remainder base n q r.val
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program (emitterLabel r)) ((ambient, r), register)
    (unaryTapes source quotient remainder base n q 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atEmitter]
  unfold emitterWithFinish
  rw [stepAux_pushWord]
  simp only [unaryTapes, MachineCopy.forkTapes_right, List.reverse_replicate]
  rw [update_remainder]
  cases exit <;>
    simp [TM2.stepAux, Reduction.MachineTransfer.exitAt, encodeWord, List.append_assoc]

theorem divModTraceWithFinish [Fintype σ] (d : Nat) (positive : 0 < d)
    (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (finish : σ → Fin d → σ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) =
      emitterWithFinish d positive remainder exit finish r)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive 0), register),
        unaryTapes source quotient remainder base n 0 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨exit, ((finish ambient (residue d positive n), residue d positive 0), none),
        unaryTapes source quotient remainder base 0 (n / d) (n % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hscan := scanTrace_fromCount d positive source quotient remainder
    sourceQuotient sourceRemainder quotientRemainder scanLabel emitterLabel program atScan
    base n 0 sourceSuffix quotientSuffix remainderSuffix ambient register
  simp only [Nat.zero_add, Nat.zero_div] at hscan
  rw [Function.iterate_succ_apply', hscan, MachineComposition.advance_some]
  exact emitterWithFinishStep d positive source quotient remainder emitterLabel exit finish
    program atEmitter base 0 (n / d) sourceSuffix quotientSuffix remainderSuffix ambient
    (residue d positive n) (some false)

theorem divModFromTapesWithFinish [Fintype σ] (d : Nat) (positive : 0 < d)
    (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (finish : σ → Fin d → σ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) =
      emitterWithFinish d positive remainder exit finish r)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base source = encodeWord n ++ sourceSuffix)
    (quotientInput : base quotient = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base remainder = encodeWord 0 ++ remainderSuffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive 0), register), base⟩) =
      some ⟨exit, ((finish ambient (residue d positive n), residue d positive 0), none),
        unaryTapes source quotient remainder base 0 (n / d) (n % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hbase : unaryTapes source quotient remainder base n 0 0 sourceSuffix quotientSuffix
      remainderSuffix = base := by
    simp only [unaryTapes, ← sourceInput, ← quotientInput, ← remainderInput,
      MachineCopy.forkTapes_self]
  have h := divModTraceWithFinish d positive source quotient remainder sourceQuotient
    sourceRemainder quotientRemainder scanLabel emitterLabel exit finish program atScan
    atEmitter base n sourceSuffix quotientSuffix remainderSuffix ambient register
  rw [hbase] at h
  exact h

end BinPackingGames.Foundations.Complexity.MachineFixedDivMod

namespace BinPackingGames.Foundations.Complexity.MachinePortReindex

open Turing MachineComposition
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) (d : Nat) := MachineFixedDivMod.State A d

def clean (d : Nat) (positive : 0 < d) (ambient : A) : State A d :=
  ((ambient, MachineFixedDivMod.residue d positive 0), none)

inductive Label (d : Nat)
  | copySeed | copyScan | copyRestore | initialize | divide
  | emit (r : Fin d)
  | affineScan | affineRestore | drainQuotient | finish
  deriving DecidableEq, Fintype

def exitAt {d : Nat} (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A d) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def emit (d : Nat) (positive : 0 < d) (output : K) (b : Nat)
    (r : Fin d) (next : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A d) :=
  pushWord output (List.replicate (r.val + b) true)
    (.load (fun s => clean d positive s.1.1) (.goto fun _ => next))

def instruction (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 5 → K) (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (Alphabet (K := K)) Λ (State A d)
  | .copySeed => MachineUnaryAffineAt.seed (tape 2) 0 (labels .copyScan)
  | .copyScan => MachineUnaryAffineAt.scan (tape 0) (tape 1) (tape 2) 1
      (labels .copyScan) (labels .copyRestore)
  | .copyRestore => Reduction.MachineTransfer.loopAt (tape 1) (tape 0) id false
      (labels .copyRestore) (some (labels .initialize))
  | .initialize => .push (tape 3) (fun _ => false)
      (.push (tape 4) (fun _ => false) (.goto fun _ => labels .divide))
  | .divide => MachineFixedDivMod.scanLoop d positive (tape 2) (tape 3)
      (labels .divide) (fun r => labels (.emit r))
  | .emit r => emit d positive (tape 4) b r (labels .affineScan)
  | .affineScan => MachineUnaryAffineAt.scan (tape 3) (tape 1) (tape 4) c
      (labels .affineScan) (labels .affineRestore)
  | .affineRestore => Reduction.MachineTransfer.loopAt (tape 1) (tape 3) id false
      (labels .affineRestore) (some (labels .drainQuotient))
  | .drainQuotient => MachineDrain.drain (tape 3) (labels .drainQuotient)
      (some (labels .finish))
  | .finish => .pop (tape 2) (fun s _ => clean d positive s.1.1) (exitAt exit)

def steps (d j : Nat) : Nat := 3 * j + 3 * (j / d) + 11

theorem steps_le (d j : Nat) : steps d j ≤ 6 * j + 11 := by
  have h := Nat.div_le_self j d
  unfold steps
  omega

theorem steps_le_encodedLength (d j : Nat) :
    steps d j ≤ 6 * (encodeWord j).length + 5 := by
  have h := steps_le d j
  rw [encodeWord_length]
  omega

def value (d c b j : Nat) : Nat := c * (j / d) + (j % d) + b

private def frame (tape : Fin 5 → K) (base : K → List Bool)
    (work quotient output : List Bool) : K → List Bool :=
  MachineCopy.forkTapes (tape 2) (tape 3) (tape 4) base work quotient output

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem reindexTrace (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A d))
    (atLabels : ∀ l, program (labels l) = instruction d positive c b tape labels exit l)
    (base : K → List Bool) (j : Nat) (suffix : List Bool)
    (sourceWord : base (tape 0) = encodeWord j ++ suffix)
    (scratchEmpty : base (tape 1) = []) (workEmpty : base (tape 2) = [])
    (quotientEmpty : base (tape 3) = []) (ambient : A) :
    (advance (TM2.step program))^[steps d j]
      (some ⟨some (labels .copySeed), clean d positive ambient, base⟩) =
      some ⟨exit, clean d positive ambient,
        Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4))⟩ := by
  have hd (i k : Fin 5) (h : i ≠ k) : tape i ≠ tape k := fun e => h (distinct e)
  let q := j / d
  let r := MachineFixedDivMod.residue d positive j
  let copied := Function.update base (tape 2) (encodeWord j)
  let initialized := frame tape base (encodeWord j) (encodeWord 0)
    (encodeWord 0 ++ base (tape 4))
  let divided := frame tape base (encodeWord 0) (encodeWord q)
    (encodeWord 0 ++ base (tape 4))
  let emitted := frame tape base (encodeWord 0) (encodeWord q)
    (encodeWord (r.val + b) ++ base (tape 4))
  let computed := frame tape base (encodeWord 0) (encodeWord q)
    (encodeWord (c * q + (r.val + b)) ++ base (tape 4))
  let drained := frame tape base (encodeWord 0) []
    (encodeWord (c * q + (r.val + b)) ++ base (tape 4))
  have copyRun : (advance (TM2.step program))^[2 * (j + 1) + 1]
      (some ⟨some (labels .copySeed), clean d positive ambient, base⟩) =
      some ⟨some (labels .initialize), clean d positive ambient, copied⟩ := by
    simpa only [clean, copied, Nat.one_mul, Nat.add_zero, workEmpty, List.append_nil] using
      MachineUnaryAffineAt.seededAffineTrace (tape 0) (tape 1) (tape 2)
        (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide)) 1 0
        (labels .copySeed) (labels .copyScan) (labels .copyRestore)
        (some (labels .initialize)) program (atLabels .copySeed) (atLabels .copyScan)
        (atLabels .copyRestore) base j suffix sourceWord scratchEmpty
        (ambient, MachineFixedDivMod.residue d positive 0) none
  have initRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .initialize), clean d positive ambient, copied⟩) =
      some ⟨some (labels .divide), clean d positive ambient, initialized⟩ := by
    change some (TM2.stepAux (program (labels .initialize)) _ _) = _
    rw [atLabels]
    simp [instruction, TM2.stepAux, copied, initialized, frame, MachineCopy.forkTapes,
      hd 3 2 (by decide), hd 4 2 (by decide), hd 4 3 (by decide), quotientEmpty, encodeWord]
  have divisionInput : MachineFixedDivMod.unaryTapes (tape 2) (tape 3) (tape 4)
      base j 0 0 [] [] (base (tape 4)) = initialized := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      List.append_nil, initialized, frame]
  have divisionOutput : MachineFixedDivMod.unaryTapes (tape 2) (tape 3) (tape 4)
      base 0 q 0 [] [] (base (tape 4)) = divided := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      List.append_nil, divided, frame]
  have divideRun : (advance (TM2.step program))^[j + 1]
      (some ⟨some (labels .divide), clean d positive ambient, initialized⟩) =
      some ⟨some (labels (.emit r)), ((ambient, r), some false), divided⟩ := by
    have h := MachineFixedDivMod.scanTrace_fromCount d positive (tape 2) (tape 3) (tape 4)
      (hd 2 3 (by decide)) (hd 2 4 (by decide)) (hd 3 4 (by decide))
      (labels .divide) (fun a => labels (.emit a)) program (atLabels .divide)
      base j 0 [] [] (base (tape 4)) ambient none
    simpa only [Nat.zero_div, Nat.zero_add, divisionInput, divisionOutput, clean, r, q] using h
  have emitRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels (.emit r)), ((ambient, r), some false), divided⟩) =
      some ⟨some (labels .affineScan), clean d positive ambient, emitted⟩ := by
    change some (TM2.stepAux (program (labels (.emit r))) _ _) = _
    rw [atLabels]
    simp [instruction, emit, stepAux_pushWord, TM2.stepAux, divided, emitted, frame,
      MachineCopy.forkTapes, List.reverse_replicate, encodeWord, List.append_assoc]
  have affineInput : MachineUnaryAffineAt.tapes (tape 3) (tape 1) (tape 4)
      emitted (encodeWord q ++ []) [] (encodeWord (r.val + b) ++ base (tape 4)) = emitted := by
    have heq : emitted (tape 3) = encodeWord q := by
      simp [emitted, frame, MachineCopy.forkTapes, hd 3 4 (by decide)]
    have hempty : emitted (tape 1) = [] := by
      simp [emitted, frame, MachineCopy.forkTapes, hd 1 2 (by decide),
        hd 1 3 (by decide), hd 1 4 (by decide), scratchEmpty]
    have hout : emitted (tape 4) = encodeWord (r.val + b) ++ base (tape 4) := by
      simp [emitted, frame, MachineCopy.forkTapes]
    rw [List.append_nil, ← heq, ← hempty, ← hout]
    exact MachineCopy.forkTapes_self _ _ _ _
  have affineOutput : MachineUnaryAffineAt.tapes (tape 3) (tape 1) (tape 4)
      emitted (encodeWord q ++ []) [] (encodeWord (c * q + (r.val + b)) ++ base (tape 4)) =
      computed := by
    funext k
    by_cases h1 : k = tape 1
    · subst k
      simp [MachineUnaryAffineAt.tapes, emitted, computed, frame, MachineCopy.forkTapes,
        hd 1 2 (by decide), hd 1 3 (by decide), hd 1 4 (by decide), scratchEmpty]
    · by_cases h3 : k = tape 3
      · subst k
        simp [MachineUnaryAffineAt.tapes, emitted, computed, frame, MachineCopy.forkTapes,
          hd 3 1 (by decide), hd 3 4 (by decide)]
      · by_cases h4 : k = tape 4
        · subst k; simp [MachineUnaryAffineAt.tapes, computed, frame, MachineCopy.forkTapes]
        · simp [MachineUnaryAffineAt.tapes, emitted, computed, frame, MachineCopy.forkTapes,
            h1, h3, h4]
  have affineRun : (advance (TM2.step program))^[2 * (q + 1)]
      (some ⟨some (labels .affineScan), clean d positive ambient, emitted⟩) =
      some ⟨some (labels .drainQuotient), clean d positive ambient, computed⟩ := by
    have h := MachineUnaryAffineAt.affineTrace (tape 3) (tape 1) (tape 4)
      (hd 3 1 (by decide)) (hd 3 4 (by decide)) (hd 1 4 (by decide)) c
      (labels .affineScan) (labels .affineRestore) (some (labels .drainQuotient))
      program (atLabels .affineScan) (atLabels .affineRestore) emitted q (r.val + b)
      [] (base (tape 4)) (ambient, MachineFixedDivMod.residue d positive 0) none
    simpa only [affineInput, affineOutput, clean] using h
  have quotientWord : computed (tape 3) = encodeWord q := by
    simp [computed, frame, MachineCopy.forkTapes, hd 3 4 (by decide)]
  have drainOutput : Function.update computed (tape 3) [] = drained := by
    funext k
    by_cases h3 : k = tape 3
    · subst k
      simp [drained, frame, MachineCopy.forkTapes, hd 3 4 (by decide)]
    · by_cases h4 : k = tape 4
      · subst k
        simp [computed, drained, frame, MachineCopy.forkTapes, hd 4 3 (by decide)]
      · simp [computed, drained, frame, MachineCopy.forkTapes, h3, h4]
  have drainRun : (advance (TM2.step program))^[q + 2]
      (some ⟨some (labels .drainQuotient), clean d positive ambient, computed⟩) =
      some ⟨some (labels .finish), clean d positive ambient, drained⟩ := by
    have h := MachineDrain.drainTrace (tape 3) (labels .drainQuotient)
      (some (labels .finish)) program (atLabels .drainQuotient)
      computed (computed (tape 3)) (ambient, MachineFixedDivMod.residue d positive 0) none
    rw [Function.update_eq_self, drainOutput, quotientWord, encodeWord_length] at h
    exact h
  have finishOutput : Function.update drained (tape 2) [] =
      Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4)) := by
    have hv : c * q + (r.val + b) = value d c b j := by
      simp [value, q, r, MachineFixedDivMod.residue, Nat.add_assoc]
    funext k
    by_cases h2 : k = tape 2
    · subst k
      simp [hd 2 4 (by decide), workEmpty]
    · by_cases h3 : k = tape 3
      · subst k
        simp [drained, frame, MachineCopy.forkTapes, hd 3 2 (by decide),
          hd 3 4 (by decide), quotientEmpty]
      · by_cases h4 : k = tape 4
        · subst k
          simp [drained, frame, MachineCopy.forkTapes, hd 4 2 (by decide), hv]
        · simp [drained, frame, MachineCopy.forkTapes, h2, h3, h4]
  have finishRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .finish), clean d positive ambient, drained⟩) =
      some ⟨exit, clean d positive ambient,
        Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4))⟩ := by
    have hw : drained (tape 2) = encodeWord 0 := by
      simp [drained, frame, MachineCopy.forkTapes, hd 2 3 (by decide), hd 2 4 (by decide)]
    change some (TM2.stepAux (program (labels .finish)) _ _) = _
    rw [atLabels]
    cases exit <;> simp [instruction, TM2.stepAux, exitAt, hw, encodeWord, finishOutput, clean]
  have total := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace copyRun initRun) divideRun) emitRun) affineRun) drainRun) finishRun
  have hsteps : steps d j =
      (((((2 * (j + 1) + 1) + 1) + (j + 1)) + 1) + 2 * (q + 1)) + (q + 2) + 1 := by
    dsimp [steps, q]
    omega
  rw [hsteps]
  exact total

def reindexInTime (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A d))
    (atLabels : ∀ l, program (labels l) = instruction d positive c b tape labels exit l)
    (base : K → List Bool) (j : Nat) (suffix : List Bool)
    (sourceWord : base (tape 0) = encodeWord j ++ suffix)
    (scratchEmpty : base (tape 1) = []) (workEmpty : base (tape 2) = [])
    (quotientEmpty : base (tape 3) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copySeed), clean d positive ambient, base⟩
      (some ⟨exit, clean d positive ambient,
        Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4))⟩)
      (6 * j + 11) where
  steps := steps d j
  evals_in_steps := reindexTrace d positive c b tape distinct labels exit program atLabels
    base j suffix sourceWord scratchEmpty workEmpty quotientEmpty ambient
  steps_le_m := steps_le d j

def machine (d : Nat) (positive : 0 < d) (c b : Nat) : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Label d
  main := .copySeed
  σ := State Unit d
  initialState := clean d positive ()
  m := instruction d positive c b id id none

def machineInTime (d : Nat) (positive : 0 < d) (c b : Nat)
    (base : Fin 5 → List Bool) (j : Nat) (suffix : List Bool)
    (sourceWord : base 0 = encodeWord j ++ suffix)
    (scratchEmpty : base 1 = []) (workEmpty : base 2 = [])
    (quotientEmpty : base 3 = []) :
    StateTransition.EvalsToInTime (machine d positive c b).step
      ⟨some .copySeed, clean d positive (), base⟩
      (some ⟨none, clean d positive (),
        Function.update base (4 : Fin 5) (encodeWord (value d c b j) ++ base 4)⟩)
      (6 * j + 11) :=
  reindexInTime d positive c b id (fun _ _ h => h) id none
    (instruction d positive c b id id none) (fun _ => rfl)
    base j suffix sourceWord scratchEmpty workEmpty quotientEmpty ()

theorem lazy_value (d j : Nat) : value d (2 * d) d j =
    2 * d * (j / d) + d + (j % d) := by
  unfold value
  omega

end BinPackingGames.Foundations.Complexity.MachinePortReindex

end OAI
