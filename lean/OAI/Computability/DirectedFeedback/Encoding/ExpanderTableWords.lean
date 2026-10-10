import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineRegularMetadata

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

namespace DFVSGames.Foundations.PCP.ExpanderTableWords

open ExpanderTables
open DFVSGames.Foundations.Complexity (encodeWords decodeWords)

variable {v d : ℕ}

def rotationWords (table : Table v d) : List Nat := table.rows.toList.map Fin.val

@[simp] theorem rotationWords_length (table : Table v d) :
    (rotationWords table).length = v * d := by
  simp [rotationWords]

theorem rotationWords_getElem (table : Table v d) (i : ℕ) (hi : i < v * d) :
    (rotationWords table)[i]'(by simpa only [rotationWords_length] using hi) =
      (reverseIndex table ⟨i, hi⟩).val := by
  simp only [rotationWords, List.getElem_map, Vector.getElem_toList,
    reverseIndex, Fin.getElem_fin]

theorem rotationWords_get (table : Table v d) (i : Fin (v * d)) :
    (rotationWords table).get
      ⟨i.val, by simpa only [rotationWords_length] using i.isLt⟩ =
      (reverseIndex table i).val := by
  simpa only [List.get_eq_getElem] using rotationWords_getElem table i.val i.isLt

theorem rotationWords_getElem? (table : Table v d) (i : Fin (v * d)) :
    (rotationWords table)[i.val]? = some (reverseIndex table i).val := by
  apply List.getElem?_eq_some_iff.mpr
  exact ⟨by simpa only [rotationWords_length] using i.isLt,
    rotationWords_getElem table i.val i.isLt⟩

theorem rotationWords_getElem?_none (table : Table v d) (i : ℕ) (hi : v * d ≤ i) :
    (rotationWords table)[i]? = none :=
  List.getElem?_eq_none (by simpa only [rotationWords_length] using hi)

theorem rotationWords_entry_lt (table : Table v d) (n : ℕ)
    (hn : n ∈ rotationWords table) : n < v * d := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hn
  exact a.isLt

theorem rotationWords_lookup (table : Table v d) (x : Fin v × Fin d) :
    (rotationWords table)[(rowIndex v d x).val]? =
      some (rowIndex v d (lookup table x)).val := by
  simpa only [lookup, Equiv.apply_symm_apply] using
    rotationWords_getElem? table (rowIndex v d x)

theorem rotationWords_row_order (table : Table v d) (x : Fin v × Fin d) :
    (rotationWords table)[x.2.val + d * x.1.val]? =
      some ((lookup table x).2.val + d * (lookup table x).1.val) := by
  simpa only [rowIndex_val] using rotationWords_lookup table x

@[simp] theorem decode_rotationWords (table : Table v d) :
    decodeWords (encodeWords (rotationWords table)) = some (rotationWords table) :=
  Complexity.decodeWords_encodeWords _

theorem decoded_lookup (table : Table v d) (i : Fin (v * d)) :
    (decodeWords (encodeWords (rotationWords table))).bind (fun words => words[i.val]?) =
      some (reverseIndex table i).val := by
  rw [decode_rotationWords]
  exact rotationWords_getElem? table i

theorem decoded_coordinate_lookup (table : Table v d) (x : Fin v × Fin d) :
    (decodeWords (encodeWords (rotationWords table))).bind
        (fun words => words[x.2.val + d * x.1.val]?) =
      some ((lookup table x).2.val + d * (lookup table x).1.val) := by
  rw [decode_rotationWords]
  exact rotationWords_row_order table x

theorem encode_rotationWords_length_eq (table : Table v d) :
    (encodeWords (rotationWords table)).length = (rotationWords table).sum + v * d := by
  rw [Complexity.encodeWords_length, rotationWords_length]

theorem encode_rotationWords_length_le (table : Table v d) :
    (encodeWords (rotationWords table)).length ≤ (v * d) * (v * d + 1) := by
  calc
    _ ≤ (rotationWords table).length * (v * d + 1) :=
      Complexity.encodeWords_length_le _ _
        (fun n hn => (rotationWords_entry_lt table n hn).le)
    _ = _ := by rw [rotationWords_length]

end DFVSGames.Foundations.PCP.ExpanderTableWords
end

section

namespace DFVSGames.Foundations.Complexity.MachineFixedDivMod

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

private theorem update_source_inline_MachineFixedDivMod (source quotient remainder : K)
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

private theorem update_quotient_inline_MachineFixedDivMod (source quotient remainder : K)
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

private theorem update_remainder_inline_MachineFixedDivMod (source quotient remainder : K) (base : K → List Bool)
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
      update_source_inline_MachineFixedDivMod, update_quotient_inline_MachineFixedDivMod, hcarry]

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
    update_source_inline_MachineFixedDivMod]

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
  rw [update_remainder_inline_MachineFixedDivMod]
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
  rw [update_remainder_inline_MachineFixedDivMod]
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

end DFVSGames.Foundations.Complexity.MachineFixedDivMod

end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

inductive Tape
  | inputVertex | table | output
  | emitScratch | queryReverse | queryIndex
  | lookupOutput | lookupWork | lookupRestore
  | quotientFirst | quotientSecond | remainderFirst | remainderSecond
  deriving DecidableEq

instance : Fintype Tape := derive_fintype% Tape

inductive Label (d : Nat)
  | initialize
  | firstEmit (label : PCP.AlphabetTable.Emitter.Label 3 (degree d))
  | firstReverse
  | firstLookup (label : MachinePreservingLookupClean.Label)
  | firstScan
  | firstResidue (r : Fin (degree d))
  | clearQuery
  | secondEmit (label : PCP.AlphabetTable.Emitter.Label 3 (degree d))
  | secondReverse
  | secondLookup (label : MachinePreservingLookupClean.Label)
  | secondScan
  | secondResidue (r : Fin (degree d))
  | outputEmit (label : PCP.AlphabetTable.Emitter.Label 3 (rowFactor d))
  | cleanup (i : Fin 6)
  | done
  deriving DecidableEq, Fintype

abbrev Ambient (ρ : Type) (d : Nat) := ρ × Control d
abbrev State (ρ : Type) (d : Nat) :=
  PCP.AlphabetTable.Emitter.State (Ambient ρ d × Fin (degree d))

def divisionStates (ρ : Type) (d : Nat) :
    MachineFixedDivMod.State (Ambient ρ d × Unit) (degree d) ≃ State ρ d where
  toFun s := (((s.1.1.1, s.1.2), ()), s.2)
  invFun s := (((s.1.1.1, ()), s.1.1.2), s.2)
  left_inv := by rintro ⟨⟨⟨a, u⟩, r⟩, b⟩; cases u; rfl
  right_inv := by rintro ⟨⟨⟨a, r⟩, u⟩, b⟩; cases u; rfl

def firstFinish {ρ : Type} {d : Nat} (s : Ambient ρ d × Unit)
    (r : Fin (degree d)) : Ambient ρ d × Unit :=
  ((s.1.1, receiveFirst s.1.2 r), ())

def secondFinish {ρ : Type} {d : Nat} (H : Table (cloudSize d) d)
    (s : Ambient ρ d × Unit) (r : Fin (degree d)) : Ambient ρ d × Unit :=
  ((s.1.1, receiveSecond H s.1.2 r), ())

def affinePlan {σ : Type} {bound : Nat} (coefficient : Nat) (offset : σ → Fin bound) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 σ bound :=
  PCP.AlphabetTable.Emitter.listCommands
    (PCP.AlphabetTable.Emitter.affineCommands [(0, coefficient)] offset)

def firstPlan (ρ : Type) (d : Nat) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 (Ambient ρ d × Fin (degree d)) (degree d) :=
  affinePlan (degree d) (fun s => firstOffset s.1.2)

def secondPlan (ρ : Type) (d : Nat) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 (Ambient ρ d × Fin (degree d)) (degree d) :=
  affinePlan (degree d) (fun s => secondOffset s.1.2)

def outputPlan (ρ : Type) (d : Nat) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 (Ambient ρ d × Fin (degree d)) (rowFactor d) :=
  affinePlan (rowFactor d) (fun s => outputOffset s.1.2)

def lookupTape : Fin 5 → Tape
  | ⟨0, _⟩ => .table
  | ⟨1, _⟩ => .queryIndex
  | ⟨2, _⟩ => .lookupWork
  | ⟨3, _⟩ => .lookupOutput
  | _ => .lookupRestore

def dirtyTape : Fin 6 → Tape
  | ⟨0, _⟩ => .queryIndex
  | ⟨1, _⟩ => .lookupOutput
  | ⟨2, _⟩ => .quotientFirst
  | ⟨3, _⟩ => .quotientSecond
  | ⟨4, _⟩ => .remainderFirst
  | _ => .remainderSecond

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

def statement {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d)
  | .initialize =>
    .push (ports .quotientFirst) (fun _ => false)
      (.push (ports .quotientSecond) (fun _ => false)
        (.push (ports .remainderFirst) (fun _ => false)
          (.push (ports .remainderSecond) (fun _ => false)
            (.load (fun s => (s.1, none))
              (.goto fun _ => labels (.firstEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry)))))))
  | .firstEmit l =>
    PCP.AlphabetTable.Emitter.statement (firstPlan ρ d) (fun _ => ports .inputVertex)
      (ports .emitScratch) (ports .queryReverse) (fun k => labels (.firstEmit k))
      (some (labels .firstReverse)) l
  | .firstReverse =>
    Reduction.MachineTransfer.loopAt (ports .queryReverse) (ports .queryIndex)
      id false (labels .firstReverse)
      (some (labels (.firstLookup (.run .copyFirst))))
  | .firstLookup l =>
    MachinePreservingLookupClean.statement (ports ∘ lookupTape)
      (fun k => labels (.firstLookup k)) (some (labels .firstScan)) l
  | .firstScan =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientFirst) (labels .firstScan)
        (fun r => labels (.firstResidue r)))
  | .firstResidue r =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
        (ports .remainderFirst) (some (labels .clearQuery)) firstFinish r)
  | .clearQuery =>
    .pop (ports .queryIndex) (fun s _ => s)
      (.pop (ports .lookupOutput) (fun s _ => s)
        (.goto fun _ => labels (.secondEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
  | .secondEmit l =>
    PCP.AlphabetTable.Emitter.statement (secondPlan ρ d) (fun _ => ports .quotientFirst)
      (ports .emitScratch) (ports .queryReverse) (fun k => labels (.secondEmit k))
      (some (labels .secondReverse)) l
  | .secondReverse =>
    Reduction.MachineTransfer.loopAt (ports .queryReverse) (ports .queryIndex)
      id false (labels .secondReverse)
      (some (labels (.secondLookup (.run .copyFirst))))
  | .secondLookup l =>
    MachinePreservingLookupClean.statement (ports ∘ lookupTape)
      (fun k => labels (.secondLookup k)) (some (labels .secondScan)) l
  | .secondScan =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientSecond) (labels .secondScan)
        (fun r => labels (.secondResidue r)))
  | .secondResidue r =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
        (ports .remainderSecond)
        (some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
        (secondFinish H) r)
  | .outputEmit l =>
    PCP.AlphabetTable.Emitter.statement (outputPlan ρ d) (fun _ => ports .quotientSecond)
      (ports .emitScratch) (ports .output) (fun k => labels (.outputEmit k))
      (some (labels (.cleanup 0))) l
  | .cleanup i =>
    MachineDrain.drain (ports (dirtyTape i)) (labels (.cleanup i))
      (some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩) else labels .done))
  | .done => Reduction.MachineTransfer.exitAt (ports .output) exit

def program {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d) :
    Label d → TM2.Stmt (fun _ : Tape => Bool) (Label d) (State ρ d) :=
  statement positive H id id none

end DFVSGames.Foundations.Complexity.MachineExpanderRow
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
