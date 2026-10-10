import Mathlib.Tactic.FinCases
import OAI.Computability.BinPacking.Computation.MachineCloudPadding
import OAI.Computability.BinPacking.PCP.PreprocessingLazyWords

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineAppendAt

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

abbrev Alphabet (β : Type) (_ : K) := β

def appendTapes (source destination : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source destination base []
    (base destination ++ base source)

@[simp] theorem appendTapes_source (source destination : K)
    (distinct : source ≠ destination) (base : K → List β) :
    appendTapes source destination base source = [] := by
  simp [appendTapes, distinct]

@[simp] theorem appendTapes_destination (source destination : K) (base : K → List β) :
    appendTapes source destination base destination = base destination ++ base source := by
  simp [appendTapes]

theorem appendTapes_other (source destination k : K)
    (notSource : k ≠ source) (notDestination : k ≠ destination) (base : K → List β) :
    appendTapes source destination base k = base k := by
  simp [appendTapes, Reduction.MachineTransfer.tapesAt, notSource, notDestination]

theorem appendTapes_scratch (source destination scratch : K)
    (sourceScratch : source ≠ scratch) (destinationScratch : destination ≠ scratch)
    (base : K → List β) (scratchEmpty : base scratch = []) :
    appendTapes source destination base scratch = [] := by
  rw [appendTapes_other source destination scratch (Ne.symm sourceScratch)
    (Ne.symm destinationScratch) base, scratchEmpty]

private def firstTapes (destination scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt destination scratch base [] (base destination).reverse

private def secondTapes (source destination scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source scratch (firstTapes destination scratch base) []
    ((base source).reverse ++ (base destination).reverse)

private theorem finalTapes_eq (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (base : K → List β)
    (scratchEmpty : base scratch = []) :
    Reduction.MachineTransfer.tapesAt scratch destination
      (secondTapes source destination scratch base) [] (base destination ++ base source) =
        appendTapes source destination base := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [appendTapes, secondTapes, firstTapes, Reduction.MachineTransfer.tapesAt,
      sourceDestination, sourceScratch]
  · by_cases hd : k = destination
    · subst k
      simp [appendTapes, Reduction.MachineTransfer.tapesAt]
    · by_cases ht : k = scratch
      · subst k
        simp [appendTapes, Reduction.MachineTransfer.tapesAt, Ne.symm sourceScratch,
          Ne.symm destinationScratch, scratchEmpty]
      · simp [appendTapes, secondTapes, firstTapes, Reduction.MachineTransfer.tapesAt,
          hs, hd, ht]

theorem appendTrace (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (fallback : β) (firstLabel secondLabel thirdLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt destination scratch
      id fallback firstLabel (some secondLabel))
    (atSecond : program secondLabel = Reduction.MachineTransfer.loopAt source scratch
      id fallback secondLabel (some thirdLabel))
    (atThird : program thirdLabel = Reduction.MachineTransfer.loopAt scratch destination
      id fallback thirdLabel exit)
    (base : K → List β) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option β) :
    (MachineComposition.advance (TM2.step program))^[
        2 * ((base source).length + (base destination).length) + 3]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), appendTapes source destination base⟩ := by
  have first := Reduction.MachineTransfer.transferAt_fromTapes destination scratch
    destinationScratch id fallback firstLabel (some secondLabel) program atFirst
    base ambient register
  change (MachineComposition.advance (TM2.step program))^[(base destination).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) = _ at first
  simp only [List.map_id, scratchEmpty, List.append_nil] at first
  change (MachineComposition.advance (TM2.step program))^[(base destination).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨some secondLabel, (ambient, none), firstTapes destination scratch base⟩ at first
  have firstSource : firstTapes destination scratch base source = base source := by
    simp [firstTapes, Reduction.MachineTransfer.tapesAt, sourceDestination, sourceScratch]
  have firstScratch : firstTapes destination scratch base scratch =
      (base destination).reverse := by
    simp [firstTapes]
  have second := Reduction.MachineTransfer.transferAt_fromTapes source scratch
    sourceScratch id fallback secondLabel (some thirdLabel) program atSecond
    (firstTapes destination scratch base) ambient none
  change (MachineComposition.advance (TM2.step program))^[
      (firstTapes destination scratch base source).length + 1]
    (some ⟨some secondLabel, (ambient, none), firstTapes destination scratch base⟩) = _
      at second
  rw [firstSource, firstScratch] at second
  simp only [List.map_id] at second
  change (MachineComposition.advance (TM2.step program))^[(base source).length + 1]
    (some ⟨some secondLabel, (ambient, none), firstTapes destination scratch base⟩) =
      some ⟨some thirdLabel, (ambient, none), secondTapes source destination scratch base⟩
        at second
  have secondScratch : secondTapes source destination scratch base scratch =
      (base source).reverse ++ (base destination).reverse := by
    simp [secondTapes]
  have secondDestination : secondTapes source destination scratch base destination = [] := by
    simp [secondTapes, firstTapes, Reduction.MachineTransfer.tapesAt,
      Ne.symm sourceDestination, destinationScratch]
  have third := Reduction.MachineTransfer.transferAt_fromTapes scratch destination
    (Ne.symm destinationScratch) id fallback thirdLabel exit program atThird
    (secondTapes source destination scratch base) ambient none
  change (MachineComposition.advance (TM2.step program))^[
      (secondTapes source destination scratch base scratch).length + 1]
    (some ⟨some thirdLabel, (ambient, none), secondTapes source destination scratch base⟩) = _
      at third
  rw [secondScratch, secondDestination] at third
  simp only [List.map_id, List.reverse_append, List.reverse_reverse, List.append_nil,
    List.length_append, List.length_reverse] at third
  rw [finalTapes_eq source destination scratch sourceDestination sourceScratch
    destinationScratch base scratchEmpty] at third
  rw [show 2 * ((base source).length + (base destination).length) + 3 =
      ((base source).length + (base destination).length + 1) +
        (((base source).length + 1) + ((base destination).length + 1)) by omega]
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := (base source).length + 1)
    (n := (base destination).length + 1), first, second]
  exact third

def appendInTime (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (fallback : β) (firstLabel secondLabel thirdLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt destination scratch
      id fallback firstLabel (some secondLabel))
    (atSecond : program secondLabel = Reduction.MachineTransfer.loopAt source scratch
      id fallback secondLabel (some thirdLabel))
    (atThird : program thirdLabel = Reduction.MachineTransfer.loopAt scratch destination
      id fallback thirdLabel exit)
    (base : K → List β) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option β) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), appendTapes source destination base⟩)
      (2 * ((base source).length + (base destination).length) + 3) where
  steps := 2 * ((base source).length + (base destination).length) + 3
  evals_in_steps := appendTrace source destination scratch sourceDestination sourceScratch
    destinationScratch fallback firstLabel secondLabel thirdLabel exit program atFirst
    atSecond atThird base scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

end BinPackingGames.Foundations.Complexity.MachineAppendAt

namespace BinPackingGames.Foundations.Complexity.MachineTableRows

open Turing
open PCP.GraphTables

inductive Label
  | relationRead | relationRestore | reverseRead | reverseRestore
  | tailRead | tailRestore | appendOld | appendRow | appendBack
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.relationRead, .relationRestore, .reverseRead,
  .reverseRestore, .tailRead, .tailRestore, .appendOld, .appendRow, .appendBack]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

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
  convert run using 1
  rfl

theorem outputFrame (base : K → List Bool) (output k : K) (hk : k ≠ output)
    (bits : List Bool) :
    Function.update base output (base output ++ bits) k = base k := by
  simp [hk]

end BinPackingGames.Foundations.Complexity.MachineTableRows

namespace BinPackingGames.Foundations.Complexity.MachineDummyRows

open Turing
open PCP.GraphTables
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

def trueRelation : RelationTable := Vector.replicate 4096 true

def trueBits : List Bool := encodeWords (relationWords trueRelation)

theorem trueBits_length : trueBits.length = 8192 := by
  simp only [trueBits, encodeWords_length, relationWords, trueRelation,
    Vector.toList_replicate, List.map_replicate, List.sum_replicate_nat,
    List.length_replicate]
  rfl

def rowBits (v e : Nat) : List Bool := encodeWord v ++ encodeWord e ++ trueBits

theorem rowBits_length (v e : Nat) : (rowBits v e).length = v + e + 8194 := by
  simp [rowBits, trueBits_length, encodeWord_length]
  omega

theorem rowBits_eq_graph_row {n m : Nat} (v : Fin n) (e : Fin m) :
    rowBits v.val e.val = encodeWords (rowWords (⟨v, e, trueRelation⟩ : DartRow n m)) := by
  rw [MachineTableRows.rowBits_eq]
  rfl

def rowsBits (v e : Nat) : Nat → List Bool
  | 0 => []
  | count + 1 => rowBits v e ++ rowsBits v (e + 1) count

abbrev Label (d : Nat) := Unit ⊕ (Fin d × (MachineTableRows.Label ⊕ Unit))

def start (d : Nat) : Label d := .inl ()
def rowLabel {d : Nat} (p : Fin d) (stage : MachineTableRows.Label) : Label d :=
  .inr (p, .inl stage)
def bumpLabel {d : Nat} (p : Fin d) : Label d := .inr (p, .inr ())

def fields : Fin 3 → Fin 6 := fun i => i.castLE (by decide)

def afterPort {d : Nat} (p : Fin d) : Option (Label d) :=
  if h : p.val + 1 < d then some (rowLabel ⟨p.val + 1, h⟩ .relationRead) else none

def entry (d : Nat) : Option (Label d) :=
  if h : 0 < d then some (rowLabel ⟨0, h⟩ .relationRead) else none

variable {σ : Type}

abbrev Alphabet (_ : Fin 6) := Bool

def continueAt {d : Nat} (exit : Option (Label d)) :
    TM2.Stmt Alphabet (Label d) (σ × Option Bool) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

theorem stepAux_continueAt {d : Nat} (exit : Option (Label d))
    (state : σ × Option Bool) (tapes : Fin 6 → List Bool) :
    TM2.stepAux (continueAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

def program (d : Nat) : Label d → TM2.Stmt Alphabet (Label d) (σ × Option Bool)
  | .inl () => pushWord 2 trueBits.reverse
      (.load (fun state => (state.1, none)) (continueAt (entry d)))
  | .inr (p, .inl stage) => MachineTableRows.routine fields 3 4 5
      (rowLabel p) (some (bumpLabel p)) stage
  | .inr (p, .inr ()) => .push 1 (fun _ => true) (continueAt (afterPort p))

def fieldTapes (v e : Nat) (output : List Bool) : Fin 6 → List Bool :=
  ![encodeWord v, encodeWord e, trueBits, [], output, []]

def initialTapes (v e : Nat) (output : List Bool) : Fin 6 → List Bool :=
  Function.update (fieldTapes v e output) 2 []

theorem initializeStep (d v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program d) ⟨some (start d), (ambient, register), initialTapes v e output⟩ =
      some ⟨entry d, (ambient, none), fieldTapes v e output⟩ := by
  change some (TM2.stepAux (program d (start d)) (ambient, register)
    (initialTapes v e output)) = _
  simp only [start, program, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
    initialTapes, Function.update_self, List.append_nil, Function.update_idem]
  have ht : Function.update (fieldTapes v e output) 2 trueBits = fieldTapes v e output := by
    funext i
    fin_cases i <;> simp [fieldTapes]
  rw [ht, stepAux_continueAt]

theorem rowTrace {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[
        4 * (v + e + 8194) + 2 * output.length + 9]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨some (bumpLabel p), (ambient, none), fieldTapes v e (output ++ rowBits v e)⟩ := by
  have hfields (i : Fin 3) : fields i ≠ (3 : Fin 6) ∧ fields i ≠ (5 : Fin 6) := by
    fin_cases i <;> decide
  have h := MachineTableRows.appendTrace fields (3 : Fin 6) 4 5 hfields
    (by decide) (by decide) (by decide) (rowLabel p) (some (bumpLabel p))
    (program d) (fun _ => rfl) (fieldTapes v e output) rfl rfl ambient register
  have hbits : MachineTableRows.fieldBits fields (fieldTapes v e output) = rowBits v e := by
    rfl
  have hsize : MachineTableRows.fieldSize fields (fieldTapes v e output) = v + e + 8194 := by
    rw [← MachineTableRows.fieldBits_length, hbits, rowBits_length]
  have ht : Function.update (fieldTapes v e output) 4 (output ++ rowBits v e) =
      fieldTapes v e (output ++ rowBits v e) := by
    funext i
    fin_cases i <;> simp [fieldTapes]
  simpa only [hsize, hbits, show fieldTapes v e output 4 = output from rfl, ht] using h

theorem bumpStep {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool) (ambient : σ) :
    TM2.step (program d) ⟨some (bumpLabel p), (ambient, none), fieldTapes v e output⟩ =
      some ⟨afterPort p, (ambient, none), fieldTapes v (e + 1) output⟩ := by
  change some (TM2.stepAux (program d (bumpLabel p)) (ambient, none)
    (fieldTapes v e output)) = _
  simp only [bumpLabel, program, TM2.stepAux]
  rw [stepAux_continueAt]
  congr 2
  funext i
  fin_cases i <;> simp [fieldTapes, encodeWord, List.replicate_succ]

theorem rowAndBumpTrace {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[
        4 * (v + e + 8194) + 2 * output.length + 10]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨afterPort p, (ambient, none), fieldTapes v (e + 1) (output ++ rowBits v e)⟩ := by
  rw [show 4 * (v + e + 8194) + 2 * output.length + 10 =
      (4 * (v + e + 8194) + 2 * output.length + 9) + 1 by omega,
    Function.iterate_succ_apply', rowTrace, MachineComposition.advance_some]
  exact bumpStep p v e (output ++ rowBits v e) ambient

def steps (v e : Nat) (output : List Bool) : Nat → Nat
  | 0 => 0
  | count + 1 => (4 * (v + e + 8194) + 2 * output.length + 10) +
      steps v (e + 1) (output ++ rowBits v e) count

theorem suffixTrace {d : Nat} (count : Nat) (p : Fin d) (hp : p.val + count = d)
    (v e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v e output count]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨none, (ambient, none), fieldTapes v (e + count) (output ++ rowsBits v e count)⟩ := by
  induction count generalizing p v e output register with
  | zero =>
    have hlt := p.isLt
    omega
  | succ count ih =>
    rw [steps, Nat.add_comm (4 * (v + e + 8194) + 2 * output.length + 10),
      Function.iterate_add_apply, rowAndBumpTrace]
    by_cases hc : count = 0
    · subst count
      have hlast : ¬ p.val + 1 < d := by omega
      simp [afterPort, hlast, steps, rowsBits]
    · have hnext : p.val + 1 < d := by omega
      rw [afterPort, dite_eq_left hnext]
      have hh := ih ⟨p.val + 1, hnext⟩ (by change (p.val + 1) + count = d; omega)
        v (e + 1) (output ++ rowBits v e) none
      have he : (e + 1) + count = e + (count + 1) := by omega
      simpa only [rowsBits, List.append_assoc, he] using hh

theorem allTrace (d v e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v e output d + 1]
      (some ⟨some (start d), (ambient, register), initialTapes v e output⟩) =
      some ⟨none, (ambient, none), fieldTapes v (e + d) (output ++ rowsBits v e d)⟩ := by
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (program d)))^[steps v e output d]
    (TM2.step (program d) ⟨some (start d), (ambient, register), initialTapes v e output⟩) = _
  rw [initializeStep]
  by_cases hd : 0 < d
  · rw [entry, dite_eq_left hd]
    exact suffixTrace d ⟨0, hd⟩ (by simp) v e output ambient none
  · have hz : d = 0 := by omega
    subst d
    simp [entry, steps, rowsBits]

def graphRows {n m : Nat} (v : Fin n) (e : Nat) :
    (count : Nat) → e + count ≤ m → List (DartRow n m)
  | 0, _ => []
  | count + 1, h =>
      ⟨v, ⟨e, by omega⟩, trueRelation⟩ ::
        graphRows v (e + 1) count (by omega)

theorem graphRows_length {n m : Nat} (v : Fin n) (e count : Nat) (h : e + count ≤ m) :
    (graphRows v e count h).length = count := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih => simp [graphRows, ih]

theorem rowsBits_eq_graphRows {n m : Nat} (v : Fin n) (e count : Nat)
    (h : e + count ≤ m) :
    rowsBits v.val e count = encodeWords ((graphRows v e count h).flatMap rowWords) := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih =>
    simp [rowsBits, graphRows, encodeWords_append, MachineTableRows.rowBits_eq,
      rowBits, trueBits]
    exact ih (e + 1) (by omega)

def dummyRows {n : Nat} (d : Nat) (v : Fin n) : List (DartRow n (n * d)) :=
  graphRows v (d * v.val) d (by
    have h := Nat.mul_le_mul_right d (Nat.succ_le_of_lt v.isLt)
    simpa only [Nat.succ_mul, Nat.mul_comm] using h)

theorem dummyRows_length {n : Nat} (d : Nat) (v : Fin n) :
    (dummyRows d v).length = d := graphRows_length _ _ _ _

theorem dummyRowsTrace {n : Nat} (d : Nat) (v : Fin n) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v.val (d * v.val) output d + 1]
      (some ⟨some (start d), (ambient, register), initialTapes v.val (d * v.val) output⟩) =
      some ⟨none, (ambient, none), fieldTapes v.val (d * v.val + d)
        (output ++ encodeWords ((dummyRows d v).flatMap rowWords))⟩ := by
  have h := allTrace d v.val (d * v.val) output ambient register
  rw [rowsBits_eq_graphRows v (d * v.val) d (by
    have h := Nat.mul_le_mul_right d (Nat.succ_le_of_lt v.isLt)
    simpa only [Nat.succ_mul, Nat.mul_comm] using h)] at h
  exact h

theorem steps_le_bound (v e : Nat) (output : List Bool) (count : Nat) :
    steps v e output count ≤ count *
      (4 * (v + e + count + 8194) +
        2 * (output.length + count * (v + e + count + 8194)) + 10) := by
  induction count generalizing e output with
  | zero => simp [steps]
  | succ count ih =>
    let B := v + e + (count + 1) + 8194
    let C := 4 * B + 2 * (output.length + (count + 1) * B) + 10
    have hb : v + (e + 1) + count + 8194 = B := by dsimp [B]; omega
    have hi := ih (e + 1) (output ++ rowBits v e)
    rw [List.length_append, rowBits_length, hb] at hi
    have hrow : v + e + 8194 ≤ B := by dsimp [B]; omega
    have hout : output.length + (v + e + 8194) + count * B ≤
        output.length + (count + 1) * B := by
      calc
        _ ≤ output.length + B + count * B :=
          Nat.add_le_add_right (Nat.add_le_add_left hrow output.length) _
        _ = _ := by simp only [Nat.add_mul, Nat.one_mul]; omega
    have hconstant : 4 * B + 2 * (output.length + (v + e + 8194) + count * B) + 10 ≤ C := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hout) (4 * B)) 10
    have hremaining := hi.trans (Nat.mul_le_mul_left count hconstant)
    have hbody : 4 * (v + e + 8194) + 2 * output.length + 10 ≤ C := by
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 4 hrow)
        (Nat.mul_le_mul_left 2 (Nat.le_add_right output.length ((count + 1) * B)))) 10
    change (4 * (v + e + 8194) + 2 * output.length + 10) +
      steps v (e + 1) (output ++ rowBits v e) count ≤ (count + 1) * C
    calc
      _ ≤ C + count * C := Nat.add_le_add hbody hremaining
      _ = (count + 1) * C := by rw [Nat.add_mul, Nat.one_mul]; omega

def inputSize (v e : Nat) (output : List Bool) : Nat :=
  (encodeWord v).length + (encodeWord e).length + output.length

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C d *
    (Polynomial.C 4 * (Polynomial.X + Polynomial.C (d + 8192)) +
      Polynomial.C 2 * (Polynomial.X + Polynomial.C d *
        (Polynomial.X + Polynomial.C (d + 8192))) + Polynomial.C 10) + 1

theorem timePolynomial_bounds (d v e : Nat) (output : List Bool) :
    steps v e output d + 1 ≤ (timePolynomial d).eval (inputSize v e output) := by
  have h := steps_le_bound v e output d
  have hB : v + e + d + 8194 ≤ inputSize v e output + d + 8192 := by
    simp only [inputSize, encodeWord_length]
    omega
  have hO : output.length ≤ inputSize v e output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hm := Nat.mul_le_mul_left d hB
  have hinner :
      4 * (v + e + d + 8194) + 2 * (output.length + d * (v + e + d + 8194)) + 10 ≤
      4 * (inputSize v e output + d + 8192) +
        2 * (inputSize v e output + d * (inputSize v e output + d + 8192)) + 10 := by
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 4 hB)
      (Nat.mul_le_mul_left 2 (Nat.add_le_add hO hm))) 10
  have htotal := h.trans (Nat.mul_le_mul_left d hinner)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  simpa only [Nat.add_assoc] using Nat.add_le_add_right htotal 1

def machine (d : Nat) : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Label d
  main := start d
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program d

def machineInTime (d v e : Nat) (output : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine d).step
      ⟨some (start d), ((), register), initialTapes v e output⟩
      (some ⟨none, ((), none), fieldTapes v (e + d) (output ++ rowsBits v e d)⟩)
      ((timePolynomial d).eval (inputSize v e output)) where
  steps := steps v e output d + 1
  evals_in_steps := by
    convert allTrace d v e output () register using 1
    rfl
  steps_le_m := timePolynomial_bounds d v e output

def machineDummyInTime {n : Nat} (d : Nat) (v : Fin n)
    (output : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine d).step
      ⟨some (start d), ((), register), initialTapes v.val (d * v.val) output⟩
      (some ⟨none, ((), none), fieldTapes v.val (d * v.val + d)
        (output ++ encodeWords ((dummyRows d v).flatMap rowWords))⟩)
      ((timePolynomial d).eval (inputSize v.val (d * v.val) output)) where
  steps := steps v.val (d * v.val) output d + 1
  evals_in_steps := by
    convert dummyRowsTrace d v output () register using 1
    rfl
  steps_le_m := timePolynomial_bounds d v.val (d * v.val) output

theorem finalFrame (v e : Nat) (output : List Bool) :
    fieldTapes v e output 0 = encodeWord v ∧
    fieldTapes v e output 2 = trueBits ∧
    fieldTapes v e output 3 = [] ∧ fieldTapes v e output 5 = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

end BinPackingGames.Foundations.Complexity.MachineDummyRows

namespace BinPackingGames.Foundations.Complexity.MachinePaddingRows

open Turing MachineComposition

inductive Control
  | initialize | guard | bump
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.initialize, .guard, .bump]

protected theorem Control.enumList_getElem?_ctorIdx_eq (x : Control) :
    Control.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 6 ⊕ Unit
abbrev Label (d : Nat) := MachineDummyRows.Label d ⊕ Control
abbrev Alphabet : Tape → Type := MachineEmbedding.Alphabet
  (fun _ : Fin 6 => Bool) (fun _ : Unit => Bool)
abbrev State := (Unit × Option Bool) × Unit

def bodyEntry (d : Nat) (hd : 0 < d) : Label d :=
  .inl (MachineDummyRows.rowLabel ⟨0, hd⟩ .relationRead)

def extra (d : Nat) (hd : 0 < d) : Control → TM2.Stmt Alphabet (Label d) State
  | .initialize => Reduction.MachineSubstitution.pushWord (.inl 2)
      MachineDummyRows.trueBits.reverse
      (.load (fun _ => (((), none), ())) (.goto (fun _ => .inr .guard)))
  | .guard => .pop (.inr ()) (fun _ bit => (((), bit), ()))
      (.branch (fun s => s.1.2.getD false)
        (.load (fun _ => (((), none), ())) (.goto (fun _ => bodyEntry d hd)))
        (.push (.inr ()) (fun _ => false)
          (.load (fun _ => (((), none), ())) .halt)))
  | .bump => .push (.inl 0) (fun _ => true) (.goto (fun _ => .inr .guard))

def program (d : Nat) (hd : 0 < d) : Label d → TM2.Stmt Alphabet (Label d) State :=
  MachineEmbedding.program (some (.inr .bump)) (MachineDummyRows.program d) (extra d hd)

def tapes (v e fuel : Nat) (output : List Bool) : ∀ k, List (Alphabet k) :=
  MachineEmbedding.tapes (MachineDummyRows.fieldTapes v e output)
    (fun _ : Unit => encodeWord fuel)

def cfg (d : Nat) (label : Option (Label d)) (v e fuel : Nat)
    (output : List Bool) : TM2.Cfg Alphabet (Label d) State :=
  ⟨label, (((), none), ()), tapes v e fuel output⟩

theorem bodyTrace (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[MachineDummyRows.steps v e output d]
      (some (cfg d (some (bodyEntry d hd)) v e fuel output)) =
      some (cfg d (some (.inr .bump)) v (e + d) fuel
        (output ++ MachineDummyRows.rowsBits v e d)) := by
  have run := MachineDummyRows.suffixTrace d ⟨0, hd⟩ (by simp)
    v e output () none
  have lifted := liftSuccessfulTrace
    (TM2.step (MachineDummyRows.program d)) (TM2.step (program d hd))
    (MachineEmbedding.configuration (some (.inr .bump)) ()
      (fun _ : Unit => encodeWord fuel))
    (by
      intro a b h
      exact MachineEmbedding.step_simulation (some (.inr Control.bump)) ()
        (fun _ : Unit => encodeWord fuel) (MachineDummyRows.program d) (extra d hd) a b h)
    (MachineDummyRows.steps v e output d) _ _ run
  exact lifted

theorem guard_succ (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    TM2.step (program d hd) (cfg d (some (.inr .guard)) v e (fuel + 1) output) =
      some (cfg d (some (bodyEntry d hd)) v e fuel output) := by
  change some (TM2.stepAux (extra d hd .guard) _ _) = _
  simp only [extra, TM2.stepAux, tapes, MachineEmbedding.tapes_inr,
    encodeWord, List.replicate_succ, List.cons_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_true]
  congr 2
  funext k
  cases k <;> simp [tapes, MachineEmbedding.tapes, Function.update, encodeWord]

theorem guard_zero (d : Nat) (hd : 0 < d) (v e : Nat) (output : List Bool) :
    TM2.step (program d hd) (cfg d (some (.inr .guard)) v e 0 output) =
      some (cfg d none v e 0 output) := by
  change some (TM2.stepAux (extra d hd .guard) _ _) = _
  simp only [extra, TM2.stepAux, tapes, MachineEmbedding.tapes_inr,
    encodeWord, List.replicate_zero, List.nil_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_false]
  congr 2
  funext k
  cases k <;> simp [tapes, MachineEmbedding.tapes, Function.update, encodeWord]

theorem bump_step (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    TM2.step (program d hd) (cfg d (some (.inr .bump)) v e fuel output) =
      some (cfg d (some (.inr .guard)) (v + 1) e fuel output) := by
  change some (TM2.stepAux (extra d hd .bump) _ _) = _
  simp only [extra, TM2.stepAux]
  congr 2
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [tapes, MachineEmbedding.tapes,
      MachineDummyRows.fieldTapes, encodeWord, List.replicate_succ]
  | inr k => simp [tapes, MachineEmbedding.tapes]

def paddingBits (d v e : Nat) : Nat → List Bool
  | 0 => []
  | count + 1 => MachineDummyRows.rowsBits v e d ++ paddingBits d (v + 1) (e + d) count

def steps (d v e : Nat) (output : List Bool) : Nat → Nat
  | 0 => 1
  | count + 1 => (MachineDummyRows.steps v e output d + 2) +
      steps d (v + 1) (e + d) (output ++ MachineDummyRows.rowsBits v e d) count

theorem loopTrace (d : Nat) (hd : 0 < d) (count v e : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[steps d v e output count]
      (some (cfg d (some (.inr .guard)) v e count output)) =
      some (cfg d none (v + count) (e + count * d) 0
        (output ++ paddingBits d v e count)) := by
  induction count generalizing v e output with
  | zero => simpa [steps, paddingBits] using guard_zero d hd v e output
  | succ count ih =>
      rw [steps, Nat.add_comm (MachineDummyRows.steps v e output d + 2),
        Function.iterate_add_apply]
      have hb : (advance (TM2.step (program d hd)))^[MachineDummyRows.steps v e output d + 2]
          (some (cfg d (some (.inr .guard)) v e (count + 1) output)) =
          some (cfg d (some (.inr .guard)) (v + 1) (e + d) count
            (output ++ MachineDummyRows.rowsBits v e d)) := by
        rw [show MachineDummyRows.steps v e output d + 2 =
          (MachineDummyRows.steps v e output d + 1) + 1 by omega,
          Function.iterate_succ_apply, advance_some, guard_succ,
          Function.iterate_succ_apply', bodyTrace, advance_some, bump_step]
      rw [hb, ih]
      simp only [paddingBits, List.append_assoc, Nat.succ_mul]
      congr 2 <;> omega

def initialTapes (v e fuel : Nat) (output : List Bool) : ∀ k, List (Alphabet k) :=
  Function.update (tapes v e fuel output) (.inl 2) []

theorem initialize_step (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    TM2.step (program d hd)
      ⟨some (.inr .initialize), (((), none), ()), initialTapes v e fuel output⟩ =
      some (cfg d (some (.inr .guard)) v e fuel output) := by
  change some (TM2.stepAux (extra d hd .initialize) _ _) = _
  simp only [extra, Reduction.MachineSubstitution.stepAux_pushWord,
    List.reverse_reverse, initialTapes, Function.update_self, List.append_nil,
    Function.update_idem, TM2.stepAux]
  congr 2
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [tapes, MachineEmbedding.tapes,
      MachineDummyRows.fieldTapes]
  | inr k => simp [tapes, MachineEmbedding.tapes]

theorem paddingTrace (d : Nat) (hd : 0 < d) (count v e : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[steps d v e output count + 1]
      (some ⟨some (.inr .initialize), (((), none), ()), initialTapes v e count output⟩) =
      some (cfg d none (v + count) (e + count * d) 0
        (output ++ paddingBits d v e count)) := by
  rw [Function.iterate_succ_apply, advance_some, initialize_step, loopTrace]

def machine (d : Nat) (hd : 0 < d) : FinTM2 where
  K := Tape
  k₀ := .inl 0
  k₁ := .inl 4
  Γ := Alphabet
  Λ := Label d
  main := .inr .initialize
  σ := State
  initialState := (((), none), ())
  m := program d hd

def execution (d : Nat) (hd : 0 < d) (count v e : Nat) (output : List Bool) :
    StateTransition.EvalsToInTime (machine d hd).step
      ⟨some (.inr .initialize), (((), none), ()), initialTapes v e count output⟩
      (some (cfg d none (v + count) (e + count * d) 0
        (output ++ paddingBits d v e count)))
      (steps d v e output count + 1) where
  steps := steps d v e output count + 1
  evals_in_steps := by
    convert paddingTrace d hd count v e output using 1
    rfl
  steps_le_m := le_rfl

end BinPackingGames.Foundations.Complexity.MachinePaddingRows

namespace BinPackingGames.Foundations.Complexity.MachinePaddingBounds

theorem rowsBits_length_le (v e count : Nat) :
    (MachineDummyRows.rowsBits v e count).length ≤ count * (v + e + count + 8194) := by
  induction count generalizing e with
  | zero => simp [MachineDummyRows.rowsBits]
  | succ count ih =>
    have hi := ih (e + 1)
    have hb : v + (e + 1) + count + 8194 = v + e + (count + 1) + 8194 := by omega
    rw [hb] at hi
    have hr : v + e + 8194 ≤ v + e + (count + 1) + 8194 := by omega
    simp only [MachineDummyRows.rowsBits, List.length_append, MachineDummyRows.rowBits_length]
    calc
      _ ≤ (v + e + (count + 1) + 8194) +
          count * (v + e + (count + 1) + 8194) := Nat.add_le_add hr hi
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]; omega

def rowBound (d v e count : Nat) : Nat := v + count + e + (count + 1) * d + 8194

theorem rowBound_next (d v e count : Nat) :
    rowBound d (v + 1) (e + d) count = rowBound d v e (count + 1) := by
  simp only [rowBound, Nat.add_mul, Nat.one_mul]
  omega

theorem blockRow_le_rowBound (d v e count : Nat) :
    v + e + d + 8194 ≤ rowBound d v e (count + 1) := by
  simp only [rowBound, Nat.add_mul, Nat.one_mul]
  omega

theorem steps_le_bound (d v e : Nat) (output : List Bool) (count : Nat) :
    MachinePaddingRows.steps d v e output count ≤
      count * (d * (4 * rowBound d v e count +
        2 * (output.length + count * d * rowBound d v e count) + 10) + 2) + 1 := by
  induction count generalizing v e output with
  | zero => simp [MachinePaddingRows.steps]
  | succ count ih =>
    let B := rowBound d v e (count + 1)
    let C := d * (4 * B + 2 * (output.length + (count + 1) * d * B) + 10) + 2
    have hb : rowBound d (v + 1) (e + d) count = B := rowBound_next d v e count
    have hr : v + e + d + 8194 ≤ B := blockRow_le_rowBound d v e count
    have hlen : (MachineDummyRows.rowsBits v e d).length ≤ d * B :=
      (rowsBits_length_le v e d).trans (Nat.mul_le_mul_left d hr)
    have hout : (output ++ MachineDummyRows.rowsBits v e d).length + count * d * B ≤
        output.length + (count + 1) * d * B := by
      rw [List.length_append]
      calc
        _ ≤ output.length + d * B + count * d * B :=
          Nat.add_le_add_right (Nat.add_le_add_left hlen output.length) _
        _ = _ := by simp only [Nat.add_mul, Nat.one_mul]; omega
    have hi := ih (v + 1) (e + d) (output ++ MachineDummyRows.rowsBits v e d)
    rw [hb] at hi
    have hconstant :
        d * (4 * B + 2 * ((output ++ MachineDummyRows.rowsBits v e d).length +
          count * d * B) + 10) + 2 ≤ C := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left d
        (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hout) (4 * B)) 10)) 2
    have hremaining := hi.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left count hconstant) 1)
    have hcount : d * B ≤ (count + 1) * d * B := by
      simpa only [Nat.one_mul, Nat.mul_assoc] using
        Nat.mul_le_mul_right (d * B) (Nat.succ_le_succ (Nat.zero_le count))
    have hbodyOutput : output.length + d * (v + e + d + 8194) ≤
        output.length + (count + 1) * d * B :=
      Nat.add_le_add_left ((Nat.mul_le_mul_left d hr).trans hcount) output.length
    have hbodyInner : 4 * (v + e + d + 8194) +
        2 * (output.length + d * (v + e + d + 8194)) + 10 ≤
          4 * B + 2 * (output.length + (count + 1) * d * B) + 10 := by
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 4 hr)
        (Nat.mul_le_mul_left 2 hbodyOutput)) 10
    have hbody : MachineDummyRows.steps v e output d + 2 ≤ C :=
      Nat.add_le_add_right ((MachineDummyRows.steps_le_bound v e output d).trans
        (Nat.mul_le_mul_left d hbodyInner)) 2
    change (MachineDummyRows.steps v e output d + 2) +
      MachinePaddingRows.steps d (v + 1) (e + d)
        (output ++ MachineDummyRows.rowsBits v e d) count ≤ (count + 1) * C + 1
    calc
      _ ≤ C + (count * C + 1) := Nat.add_le_add hbody hremaining
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]; omega

def inputSize (v e count : Nat) (output : List Bool) : Nat :=
  (encodeWord v).length + (encodeWord e).length + (encodeWord count).length + output.length

def rowCap (d size : Nat) : Nat := size + (size + 1) * d + 8194

theorem rowBound_le_cap (d v e count : Nat) (output : List Bool) :
    rowBound d v e count ≤ rowCap d (inputSize v e count output) := by
  have hbase : v + e + count ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hcount : count ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hmul := Nat.mul_le_mul_right d (Nat.succ_le_succ hcount)
  have h := Nat.add_le_add_right (Nat.add_le_add hbase hmul) 8194
  simpa only [rowBound, rowCap, Nat.succ_eq_add_one, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h

noncomputable def rowPolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.X + (Polynomial.X + 1) * Polynomial.C d + Polynomial.C 8194

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.X * (Polynomial.C d *
    (Polynomial.C 4 * rowPolynomial d +
      Polynomial.C 2 * (Polynomial.X + Polynomial.X * Polynomial.C d * rowPolynomial d) +
      Polynomial.C 10) + Polynomial.C 2) + 1

theorem timePolynomial_bounds (d v e count : Nat) (output : List Bool) :
    MachinePaddingRows.steps d v e output count ≤
      (timePolynomial d).eval (inputSize v e count output) := by
  have hc : count ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have ho : output.length ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hb := rowBound_le_cap d v e count output
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_right d hc) hb
  have hout := Nat.add_le_add ho hp
  have hinner := Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left 4 hb) (Nat.mul_le_mul_left 2 hout)) 10
  have hbody := Nat.add_le_add_right (Nat.mul_le_mul_left d hinner) 2
  have h := (steps_le_bound d v e output count).trans
    (Nat.add_le_add_right (Nat.mul_le_mul hc hbody) 1)
  simpa only [timePolynomial, rowPolynomial, rowCap, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one] using h

end BinPackingGames.Foundations.Complexity.MachinePaddingBounds

namespace BinPackingGames.Foundations.Complexity.MachinePaddingCertificate

open MachinePaddingRows

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  MachinePaddingBounds.timePolynomial d + 1

def execution (d : Nat) (hd : 0 < d) (count v e : Nat) (output : List Bool) :
    StateTransition.EvalsToInTime (machine d hd).step
      ⟨some (.inr .initialize), (((), none), ()), initialTapes v e count output⟩
      (some (cfg d none (v + count) (e + count * d) 0
        (output ++ paddingBits d v e count)))
      ((timePolynomial d).eval (MachinePaddingBounds.inputSize v e count output)) where
  steps := steps d v e output count + 1
  evals_in_steps := by
    convert paddingTrace d hd count v e output using 1
    rfl
  steps_le_m := by
    simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.add_le_add_right
      (MachinePaddingBounds.timePolynomial_bounds d v e count output) 1

end BinPackingGames.Foundations.Complexity.MachinePaddingCertificate

namespace BinPackingGames.Foundations.Complexity.MachineLazyCodec
open PCP.GraphTables PCP.PreprocessingLazyWords

theorem rowsBits_ofFn (v e count : Nat) :
    MachineDummyRows.rowsBits v e count =
      (List.ofFn fun p : Fin count => MachineDummyRows.rowBits v (e + p.val)).flatten := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih =>
    rw [MachineDummyRows.rowsBits, List.ofFn_succ, List.flatten_cons]
    simp only [Fin.val_zero, Nat.add_zero]
    apply congrArg (MachineDummyRows.rowBits v e ++ ·)
    rw [ih]
    apply congrArg List.flatten
    congr 1
    funext p
    simp only [Fin.val_succ]
    congr 1
    omega

private theorem encodeWords_flatMap {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem rowBits_stay {n d : Nat} (v : Fin n) (p : Fin d) :
    MachineDummyRows.rowBits v.val (2 * d * v.val + p.val) =
      encodeWords (rowWords (stayRow d v p)) := by
  have h := MachineDummyRows.rowBits_eq_graph_row v (stayRow d v p).reverseIndex
  rw [stayRow_reverse_val] at h
  exact h

theorem rowsBits_stay {n d : Nat} (v : Fin n) :
    MachineDummyRows.rowsBits v.val (2 * d * v.val) d =
      encodeWords ((List.ofFn (stayRow d v)).flatMap rowWords) := by
  rw [rowsBits_ofFn, encodeWords_flatMap]
  simp only [List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  congr 1
  funext p
  exact rowBits_stay v p

end BinPackingGames.Foundations.Complexity.MachineLazyCodec

namespace BinPackingGames.Foundations.Complexity.MachineRegularDummyRow

open Turing MachineComposition PCP.GraphTables

abbrev Tape := Fin 6
abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := σ × Option Bool

inductive Label
  | affine (stage : MachineUnaryAffineAt.Label)
  | row (stage : MachineDummyRows.Label 1)
  | reverse | relation
  deriving DecidableEq, Fintype

def reverseIndex (q x : Nat) : Nat := (q + 1) * x + q

def emittedBits (q x : Nat) : List Bool :=
  MachineDummyRows.rowBits x (reverseIndex q x)

def instruction {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ (State σ)
  | .affine .seed => MachineUnaryAffineAt.seed 1 q (labels (.affine .scan))
  | .affine .scan => MachineUnaryAffineAt.scan 0 3 1 (q + 1)
      (labels (.affine .scan)) (labels (.affine .restore))
  | .affine .restore => Reduction.MachineTransfer.loopAt 3 0 id false
      (labels (.affine .restore)) (some (labels (.row (MachineDummyRows.start 1))))
  | .row stage => MachineCloudPadding.Placement.statement (id : Tape → Tape)
      (fun l => labels (.row l)) (some (labels .reverse))
      (MachineDummyRows.program 1 stage)
  | .reverse => MachineDrain.drain 1 (labels .reverse) (some (labels .relation))
  | .relation => MachineDrain.drain 2 (labels .relation) exit

structure Input (x : Nat) (base : Tape → List Bool) : Prop where
  source : base 0 = encodeWord x
  reverseEmpty : base 1 = []
  relationEmpty : base 2 = []
  scratchEmpty : base 3 = []
  rowEmpty : base 5 = []

def memory (x : Nat) (output : List Bool) : Tape → List Bool :=
  ![encodeWord x, [], [], [], output, []]

theorem memory_input (x : Nat) (output : List Bool) : Input x (memory x output) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem affine_frame (x e : Nat) (base : Tape → List Bool) (input : Input x base) :
    Function.update base 1 (encodeWord e) =
      MachineDummyRows.initialTapes x e (base 4) := by
  funext k
  fin_cases k <;>
    simp [MachineDummyRows.initialTapes, MachineDummyRows.fieldTapes,
      input.source, input.relationEmpty, input.scratchEmpty, input.rowEmpty]

theorem cleanup_frame (x e : Nat) (output : List Bool)
    (base : Tape → List Bool) (input : Input x base) :
    Function.update (Function.update (MachineDummyRows.fieldTapes x e output) 1 []) 2 [] =
      Function.update base 4 output := by
  funext k
  fin_cases k <;>
    simp [MachineDummyRows.fieldTapes, input.source, input.reverseEmpty,
      input.relationEmpty, input.scratchEmpty, input.rowEmpty]

theorem rowTraceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (x e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineDummyRows.steps x e output 1 + 1]
      (some ⟨some (labels (.row (MachineDummyRows.start 1))), (ambient, register),
        MachineDummyRows.initialTapes x e output⟩) =
      some ⟨some (labels .reverse), (ambient, none),
        MachineDummyRows.fieldTapes x (e + 1) (output ++ MachineDummyRows.rowBits x e)⟩ := by
  have run := MachineDummyRows.allTrace 1 x e output ambient register
  have placed := MachineCloudPadding.Placement.trace (id : Tape → Tape) (fun k => some k)
    (fun _ => rfl) (fun _ _ h => (Option.some.inj h).symm)
    (fun l => labels (.row l)) (some (labels .reverse)) (fun _ => [])
    (MachineDummyRows.program 1) program
    (fun l => code (.row l)) _ _ _ run
  have identityTapes (source : Tape → List Bool) :
      MachineCloudPadding.Placement.tapes (fun k : Tape => some k) source
        (fun _ : Tape => []) = source := rfl
  simpa only [MachineCloudPadding.Placement.configuration,
    MachineCloudPadding.Placement.label, identityTapes,
    MachineDummyRows.rowsBits, List.append_nil] using placed

theorem cleanupTraceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (x e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[
        ((encodeWord e).length + 1) + (MachineDummyRows.trueBits.length + 1)]
      (some ⟨some (labels .reverse), (ambient, register),
        MachineDummyRows.fieldTapes x e output⟩) =
      some ⟨exit, (ambient, none),
        Function.update (Function.update (MachineDummyRows.fieldTapes x e output) 1 []) 2 []⟩ := by
  let base := MachineDummyRows.fieldTapes x e output
  let mid := Function.update base (1 : Tape) []
  have first := MachineDrain.drainTrace (1 : Tape) (labels .reverse)
    (some (labels .relation)) program (code .reverse) base (base 1) ambient register
  have second := MachineDrain.drainTrace (2 : Tape) (labels .relation)
    exit program (code .relation) mid (mid 2) ambient none
  simp only [Function.update_eq_self] at first second
  have hreverse : base 1 = encodeWord e := rfl
  have hrelation : mid 2 = MachineDummyRows.trueBits := by
    simp only [mid, Function.update_of_ne (by decide : (2 : Tape) ≠ 1)]
    rfl
  rw [hreverse] at first
  rw [hrelation] at second
  exact join_trace first second

def steps (q x : Nat) (output : List Bool) : Nat :=
  ((2 * (x + 1) + 1) + (MachineDummyRows.steps x (reverseIndex q x) output 1 + 1)) +
    (((encodeWord (reverseIndex q x + 1)).length + 1) +
      (MachineDummyRows.trueBits.length + 1))

def timeBound (q x outputLength : Nat) : Nat :=
  (5 * q + 11) * x + 2 * outputLength + 5 * q + 40986

theorem steps_eq (q x : Nat) (output : List Bool) :
    steps q x output = timeBound q x output.length := by
  simp only [steps, MachineDummyRows.steps, encodeWord_length, MachineDummyRows.trueBits_length,
    reverseIndex, timeBound]
  ring

theorem traceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (x : Nat) (base : Tape → List Bool) (input : Input x base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps q x (base 4)]
      (some ⟨some (labels (.affine .seed)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Function.update base 4 (base 4 ++ emittedBits q x)⟩ := by
  have affine := MachineUnaryAffineAt.seededAffineTrace (0 : Tape) 3 1
    (by decide) (by decide) (by decide) (q + 1) q
    (labels (.affine .seed)) (labels (.affine .scan)) (labels (.affine .restore))
    (some (labels (.row (MachineDummyRows.start 1)))) program
    (code (.affine .seed)) (code (.affine .scan)) (code (.affine .restore))
    base x [] (by simpa only [List.append_nil] using input.source)
    input.scratchEmpty ambient register
  simp only [input.reverseEmpty, List.append_nil] at affine
  change (advance (TM2.step program))^[2 * (x + 1) + 1]
    (some ⟨some (labels (.affine .seed)), (ambient, register), base⟩) =
      some ⟨some (labels (.row (MachineDummyRows.start 1))), (ambient, none),
        Function.update base 1 (encodeWord (reverseIndex q x))⟩ at affine
  rw [affine_frame x (reverseIndex q x) base input] at affine
  have row := rowTraceAt q labels exit program code x (reverseIndex q x) (base 4) ambient none
  have clean := cleanupTraceAt q labels exit program code x (reverseIndex q x + 1)
    (base 4 ++ MachineDummyRows.rowBits x (reverseIndex q x)) ambient none
  rw [cleanup_frame x (reverseIndex q x + 1) _ base input] at clean
  exact join_trace (join_trace affine row) clean

def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 4
  Γ := Alphabet
  Λ := Label
  main := .affine .seed
  σ := State Unit
  initialState := ((), none)
  m := instruction q id none

def machineInTime (q x : Nat) (base : Tape → List Bool) (input : Input x base)
    (register : Option Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.affine .seed), ((), register), base⟩
      (some ⟨none, ((), none), Function.update base (4 : Tape)
        (base 4 ++ emittedBits q x)⟩)
      (timeBound q x (base 4).length) where
  steps := steps q x (base 4)
  evals_in_steps := traceAt q id none (instruction q id none)
    (fun _ => rfl) x base input () register
  steps_le_m := (steps_eq q x (base 4)).le

end BinPackingGames.Foundations.Complexity.MachineRegularDummyRow

end OAI
