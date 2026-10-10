import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.GraphTables
import OAI.Combinatorics.IndependentSets.Machines.MachineCopy
import OAI.Combinatorics.IndependentSets.Machines.MachineAppend

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineTableRows

open Turing
open PCP.GraphTables

inductive Label
  | relationRead | relationRestore | reverseRead | reverseRestore
  | tailRead | tailRestore | appendOld | appendRow | appendBack
  deriving DecidableEq

instance : Fintype Label where
  elems := {.relationRead, .relationRestore, .reverseRead, .reverseRestore, .tailRead,
    .tailRestore, .appendOld, .appendRow, .appendBack}
  complete value := by cases value <;> simp

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def routine (fields : Fin 3 → K) (row output scratch : K)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .relationRead => Reduction.MachineTransfer.loopAt (fields 2) scratch id false
      (labels .relationRead) (some (labels .relationRestore))
  | .relationRestore => MachineCopy.forkLoop scratch (fields 2) row false
      (labels .relationRestore) (some (labels .reverseRead))
  | .reverseRead => Reduction.MachineTransfer.loopAt (fields 1) scratch id false
      (labels .reverseRead) (some (labels .reverseRestore))
  | .reverseRestore => MachineCopy.forkLoop scratch (fields 1) row false
      (labels .reverseRestore) (some (labels .tailRead))
  | .tailRead => Reduction.MachineTransfer.loopAt (fields 0) scratch id false
      (labels .tailRead) (some (labels .tailRestore))
  | .tailRestore => MachineCopy.forkLoop scratch (fields 0) row false
      (labels .tailRestore) (some (labels .appendOld))
  | .appendOld => Reduction.MachineTransfer.loopAt output scratch id false
      (labels .appendOld) (some (labels .appendRow))
  | .appendRow => Reduction.MachineTransfer.loopAt row scratch id false
      (labels .appendRow) (some (labels .appendBack))
  | .appendBack => Reduction.MachineTransfer.loopAt scratch output id false
      (labels .appendBack) exit

def fieldBits (fields : Fin 3 → K) (base : K → List Bool) : List Bool :=
  base (fields 0) ++ base (fields 1) ++ base (fields 2)

def fieldSize (fields : Fin 3 → K) (base : K → List Bool) : Nat :=
  (base (fields 0)).length + (base (fields 1)).length + (base (fields 2)).length

omit [DecidableEq K] in
@[simp] theorem fieldBits_length (fields : Fin 3 → K) (base : K → List Bool) :
    (fieldBits fields base).length = fieldSize fields base := by
  simp [fieldBits, fieldSize, Nat.add_assoc]

def prefixTapes (fields : Fin 3 → K) (row : K) (base : K → List Bool) : K → List Bool :=
  Function.update base row (fieldBits fields base ++ base row)

theorem prefixTrace (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowScratch : row ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hscratch : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * (fieldSize fields base + 3)]
      (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
      some ⟨some (labels .appendOld), (ambient, none), prefixTapes fields row base⟩ := by
  let afterRelation := Function.update base row (base (fields 2) ++ base row)
  let afterReverse := Function.update afterRelation row
    (base (fields 1) ++ afterRelation row)
  have hfirst := MachineCopy.copyTrace (fields 2) row scratch
    (hfields 2).1 (hfields 2).2 hrowScratch false
    (labels .relationRead) (labels .relationRestore) (some (labels .reverseRead))
    program (hprogram .relationRead) (hprogram .relationRestore) base hscratch ambient register
  change (MachineComposition.advance (TM2.step program))^[2 * ((base (fields 2)).length + 1)]
    (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
    some ⟨some (labels .reverseRead), (ambient, none), afterRelation⟩ at hfirst
  have hsecond := MachineCopy.copyTrace (fields 1) row scratch
    (hfields 1).1 (hfields 1).2 hrowScratch false
    (labels .reverseRead) (labels .reverseRestore) (some (labels .tailRead))
    program (hprogram .reverseRead) (hprogram .reverseRestore) afterRelation
    (by simp [afterRelation, Ne.symm hrowScratch, hscratch]) ambient none
  have hrev : afterRelation (fields 1) = base (fields 1) := by
    simp [afterRelation, (hfields 1).1]
  rw [hrev] at hsecond
  change (MachineComposition.advance (TM2.step program))^[2 * ((base (fields 1)).length + 1)]
    (some ⟨some (labels .reverseRead), (ambient, none), afterRelation⟩) =
    some ⟨some (labels .tailRead), (ambient, none), afterReverse⟩ at hsecond
  have hthird := MachineCopy.copyTrace (fields 0) row scratch
    (hfields 0).1 (hfields 0).2 hrowScratch false
    (labels .tailRead) (labels .tailRestore) (some (labels .appendOld))
    program (hprogram .tailRead) (hprogram .tailRestore) afterReverse
    (by simp [afterReverse, afterRelation, Ne.symm hrowScratch, hscratch]) ambient none
  have htail : afterReverse (fields 0) = base (fields 0) := by
    simp [afterReverse, afterRelation, (hfields 0).1]
  rw [htail] at hthird
  have hfinal : Function.update afterReverse row
      (base (fields 0) ++ afterReverse row) = prefixTapes fields row base := by
    simp [afterReverse, afterRelation, prefixTapes, fieldBits, List.append_assoc]
  rw [hfinal] at hthird
  rw [show 2 * (fieldSize fields base + 3) =
    2 * ((base (fields 0)).length + 1) +
      (2 * ((base (fields 1)).length + 1) + 2 * ((base (fields 2)).length + 1)) by
        simp only [fieldSize]; omega,
    Function.iterate_add_apply,
    Function.iterate_add_apply (m := 2 * ((base (fields 1)).length + 1))
      (n := 2 * ((base (fields 2)).length + 1)), hfirst, hsecond]
  exact hthird

theorem appendTrace (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowOutput : row ≠ output) (hrowScratch : row ≠ scratch)
    (houtputScratch : output ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hrow : base row = []) (hscratch : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[
        4 * fieldSize fields base + 2 * (base output).length + 9]
      (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base output (base output ++ fieldBits fields base)⟩ := by
  have hprefix := prefixTrace fields row output scratch hfields hrowScratch
    labels exit program hprogram base hscratch ambient register
  have happend := MachineAppendAt.appendTrace row output scratch hrowOutput hrowScratch
    houtputScratch false (labels .appendOld) (labels .appendRow) (labels .appendBack)
    exit program (hprogram .appendOld) (hprogram .appendRow) (hprogram .appendBack)
    (prefixTapes fields row base)
    (by simp [prefixTapes, Ne.symm hrowScratch, hscratch]) ambient none
  have hrowbits : prefixTapes fields row base row = fieldBits fields base := by
    simp [prefixTapes, hrow]
  have hout : prefixTapes fields row base output = base output := by
    simp [prefixTapes, Ne.symm hrowOutput]
  rw [hrowbits, hout, fieldBits_length] at happend
  have hfinal : MachineAppendAt.appendTapes row output (prefixTapes fields row base) =
      Function.update base output (base output ++ fieldBits fields base) := by
    funext k
    by_cases ho : k = output
    · subst k
      simp [MachineAppendAt.appendTapes, hrowbits, hout]
    · by_cases hr : k = row
      · subst k
        simp [MachineAppendAt.appendTapes, Reduction.MachineTransfer.tapesAt,
          prefixTapes, hrowOutput, hrow]
      · simp [MachineAppendAt.appendTapes, Reduction.MachineTransfer.tapesAt,
          prefixTapes, ho, hr]
  rw [hfinal] at happend
  rw [show 4 * fieldSize fields base + 2 * (base output).length + 9 =
      (2 * (fieldSize fields base + (base output).length) + 3) +
        2 * (fieldSize fields base + 3) by omega,
    Function.iterate_add_apply, hprefix]
  exact happend

theorem rowBits_eq {n m : Nat} (r : DartRow n m) :
    encodeWords (rowWords r) = encodeWord r.tail.val ++
      encodeWord r.reverseIndex.val ++ encodeWords (relationWords r.relation) := by
  simp [rowWords, encodeWords]

omit [DecidableEq K] in
theorem fieldBits_eq_rowBits {n m : Nat} (r : DartRow n m)
    (fields : Fin 3 → K) (base : K → List Bool)
    (htail : base (fields 0) = encodeWord r.tail.val)
    (hreverse : base (fields 1) = encodeWord r.reverseIndex.val)
    (hrelation : base (fields 2) = encodeWords (relationWords r.relation)) :
    fieldBits fields base = encodeWords (rowWords r) := by
  rw [fieldBits, htail, hreverse, hrelation, rowBits_eq]

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 9

omit [DecidableEq K] in
theorem timePolynomial_bounds (fields : Fin 3 → K) (base : K → List Bool) (output : K) :
    4 * fieldSize fields base + 2 * (base output).length + 9 ≤
      timePolynomial.eval (fieldSize fields base + (base output).length) := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  omega

def rowAppendInTime {n m : Nat} (r : DartRow n m)
    (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowOutput : row ≠ output) (hrowScratch : row ≠ scratch)
    (houtputScratch : output ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hrow : base row = []) (hscratch : base scratch = [])
    (htail : base (fields 0) = encodeWord r.tail.val)
    (hreverse : base (fields 1) = encodeWord r.reverseIndex.val)
    (hrelation : base (fields 2) = encodeWords (relationWords r.relation))
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .relationRead), (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base output (base output ++ encodeWords (rowWords r))⟩)
      (timePolynomial.eval (fieldSize fields base + (base output).length)) where
  steps := 4 * fieldSize fields base + 2 * (base output).length + 9
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[_] _ = _
    rw [← fieldBits_eq_rowBits r fields base htail hreverse hrelation]
    exact appendTrace fields row output scratch hfields hrowOutput hrowScratch
      houtputScratch labels exit program hprogram base hrow hscratch ambient register
  steps_le_m := timePolynomial_bounds fields base output

def machine : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Label
  main := .relationRead
  σ := Unit × Option Bool
  initialState := ((), none)
  m := routine (fun i : Fin 3 => i.castLE (by decide)) 3 4 5 id none

def machineRowInTime {n m : Nat} (r : DartRow n m) (base : Fin 6 → List Bool)
    (hrow : base 3 = []) (hscratch : base 5 = [])
    (htail : base 0 = encodeWord r.tail.val)
    (hreverse : base 1 = encodeWord r.reverseIndex.val)
    (hrelation : base 2 = encodeWords (relationWords r.relation)) (register : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some .relationRead, ((), register), base⟩
      (some ⟨none, ((), none),
        Function.update base (4 : Fin 6) (base 4 ++ encodeWords (rowWords r))⟩)
      (timePolynomial.eval ((encodeWords (rowWords r)).length + (base 4).length)) := by
  let fields : Fin 3 → Fin 6 := fun i => i.castLE (by decide)
  have hfields (i : Fin 3) : fields i ≠ 3 ∧ fields i ≠ 5 := by
    constructor
    · intro h
      have he := congrArg Fin.val h
      change i.val = 3 at he
      omega
    · intro h
      have he := congrArg Fin.val h
      change i.val = 5 at he
      omega
  have hsize : fieldSize fields base = (encodeWords (rowWords r)).length := by
    rw [← fieldBits_length, fieldBits_eq_rowBits r fields base htail hreverse hrelation]
  have run := rowAppendInTime r fields (3 : Fin 6) 4 5 hfields (by decide) (by decide)
    (by decide) id none machine.m (fun _ => rfl) base hrow hscratch
    htail hreverse hrelation () register
  rw [hsize] at run
  convert run using 1; rfl

theorem outputFrame (base : K → List Bool) (output k : K) (hk : k ≠ output)
    (bits : List Bool) :
    Function.update base output (base output ++ bits) k = base k := by
  simp [hk]

end IndependentSetsGames.Foundations.Complexity.MachineTableRows

end OAI
