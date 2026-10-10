import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachinePaddedExpanderFamily
import OAI.Computability.DirectedFeedback.Machines.MachineCloudSelect

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

namespace DFVSGames.Foundations.Complexity.MachineRegularInternalRow

open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def equalityBits : List Bool :=
  encodeWords (GraphTables.relationWords PreprocessingInternalRows.equalityRelation)

theorem equalityBits_length_le : equalityBits.length ≤ 8192 :=
  GraphTables.relationBits_length_le _

def emittedBits (q x z r : Nat) : List Bool :=
  encodeWord x ++ encodeWord ((q + 1) * z + r) ++ equalityBits

theorem emittedBits_length (q x z r : Nat) :
    (emittedBits q x z r).length = x + ((q + 1) * z + r) + equalityBits.length + 2 := by
  simp only [emittedBits, List.length_append, encodeWord_length]
  omega

theorem emittedBits_eq_row (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v) (p : Fin q) :
    emittedBits q (PreprocessingRegularTables.vertexOrder t padding x.val).val
      (PreprocessingInternalRows.selectedIndex t padding v
        (PreprocessingInternalRows.localStep t padding tables v x p).1)
      (PreprocessingInternalRows.localStep t padding tables v x p).2.val =
        encodeWords (GraphTables.rowWords
          (PreprocessingInternalRows.row t padding tables v x p)) := by
  rw [MachineTableRows.rowBits_eq, PreprocessingInternalRows.row_tail,
    PreprocessingInternalRows.row_reverse_selectedIndex, PreprocessingInternalRows.row_relation]
  rfl

theorem selected_rotation {n q : Nat} (table : ExpanderTables.Table n q)
    (i : Fin n) (p : Fin q) :
    (ExpanderTableWords.rotationWords table)[q * i.val + p.val]? =
      some (q * (ExpanderTables.lookup table (i, p)).1.val +
        (ExpanderTables.lookup table (i, p)).2.val) := by
  simpa only [Nat.add_comm] using ExpanderTableWords.rotationWords_row_order table (i, p)

theorem selected_rotation_div {n q : Nat} (positive : 0 < q)
    (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) :
    (q * (ExpanderTables.lookup table (i, p)).1.val +
      (ExpanderTables.lookup table (i, p)).2.val) / q =
        (ExpanderTables.lookup table (i, p)).1.val := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ positive,
    Nat.div_eq_of_lt (ExpanderTables.lookup table (i, p)).2.isLt, Nat.zero_add]

theorem selected_rotation_mod {n q : Nat} (_positive : 0 < q)
    (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) :
    (q * (ExpanderTables.lookup table (i, p)).1.val +
      (ExpanderTables.lookup table (i, p)).2.val) % q =
        (ExpanderTables.lookup table (i, p)).2.val := by
  rw [Nat.mul_add_mod_self_left,
    Nat.mod_eq_of_lt (ExpanderTables.lookup table (i, p)).2.isLt]

theorem rotationLookupTrace {n q : Nat} (table : ExpanderTables.Table n q)
    (i : Fin n) (p : Fin q) (source : K) (tape : Fin 5 → K)
    (distinct : Function.Injective tape) (outside : ∀ a, source ≠ tape a)
    (labels : MachineAffineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ l, program (labels l) =
      MachineAffineLookup.instruction source tape q p.val labels exit l)
    (base : K → List Bool)
    (tableWord : base (tape 0) = encodeWords (ExpanderTableWords.rotationWords table))
    (scratchEmpty : base (tape 4) = []) (suffix : List Bool)
    (sourceWord : base source = encodeWord i.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineAffineLookup.steps
        (ExpanderTableWords.rotationWords table) i.val q p.val]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), MachineAffineLookup.finalTapes tape base
        (ExpanderTableWords.rotationWords table) (q * i.val + p.val)
        (q * (ExpanderTables.lookup table (i, p)).1.val +
          (ExpanderTables.lookup table (i, p)).2.val)⟩ :=
  MachineAffineLookup.affineLookupTrace source tape distinct outside q p.val labels exit
    program code base _ tableWord scratchEmpty i.val suffix sourceWord _
    (selected_rotation table i p) ambient register

inductive FinishLabel
  | seedReturn | copyReturn | restoreReturn | affine | restoreTarget | equality
  | row (stage : MachineTableRows.Label)
  | clearReverse | clearEquality
  deriving DecidableEq, Fintype

def finishFields (tape : Fin 8 → K) : Fin 3 → K := fun i =>
  if i = 0 then tape 0 else if i = 1 then tape 4 else tape 5

omit [DecidableEq K] in
@[simp] theorem finishFields_zero (tape : Fin 8 → K) : finishFields tape 0 = tape 0 := rfl
omit [DecidableEq K] in
@[simp] theorem finishFields_one (tape : Fin 8 → K) : finishFields tape 1 = tape 4 := rfl
omit [DecidableEq K] in
@[simp] theorem finishFields_two (tape : Fin 8 → K) : finishFields tape 2 = tape 5 := rfl

def finishInstruction (q : Nat) (tape : Fin 8 → K) (labels : FinishLabel → Λ)
    (exit : Option Λ) : FinishLabel → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seedReturn => MachineUnaryAffineAt.seed (tape 4) 0 (labels .copyReturn)
  | .copyReturn => MachineUnaryAffineAt.scan (tape 2) (tape 3) (tape 4) 1
      (labels .copyReturn) (labels .restoreReturn)
  | .restoreReturn => Reduction.MachineTransfer.loopAt (tape 3) (tape 2) id false
      (labels .restoreReturn) (some (labels .affine))
  | .affine => MachineUnaryAffineAt.scan (tape 1) (tape 3) (tape 4) (q + 1)
      (labels .affine) (labels .restoreTarget)
  | .restoreTarget => Reduction.MachineTransfer.loopAt (tape 3) (tape 1) id false
      (labels .restoreTarget) (some (labels .equality))
  | .equality => pushWord (tape 5) equalityBits.reverse
      (.goto fun _ => labels (.row .relationRead))
  | .row stage => MachineTableRows.routine (finishFields tape) (tape 6) (tape 7) (tape 3)
      (fun l => labels (.row l)) (some (labels .clearReverse)) stage
  | .clearReverse => MachineDrain.drain (tape 4) (labels .clearReverse)
      (some (labels .clearEquality))
  | .clearEquality => MachineDrain.drain (tape 5) (labels .clearEquality) exit

def finishSteps (q x z r outputLength : Nat) : Nat :=
  (2 * (r + 1) + 1) + 2 * (z + 1) + 1 +
    (4 * (x + ((q + 1) * z + r) + equalityBits.length + 2) + 2 * outputLength + 9) +
    (((q + 1) * z + r) + 2) + (equalityBits.length + 1)

theorem finishSteps_le (q x z r outputLength : Nat) :
    finishSteps q x z r outputLength ≤
      (5 * q + 7) * z + 7 * r + 4 * x + 2 * outputLength + 40986 := by
  have h := equalityBits_length_le
  unfold finishSteps
  nlinarith

theorem joinTrace_inline_MachineRegularInternalRow {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem finishTrace (q : Nat) (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : FinishLabel → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ l, program (labels l) = finishInstruction q tape labels exit l)
    (base : K → List Bool) (x z r : Nat)
    (tailWord : base (tape 0) = encodeWord x)
    (targetWord : base (tape 1) = encodeWord z)
    (returnWord : base (tape 2) = encodeWord r)
    (scratchEmpty : base (tape 3) = []) (reverseEmpty : base (tape 4) = [])
    (equalityEmpty : base (tape 5) = []) (rowEmpty : base (tape 6) = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[finishSteps q x z r (base (tape 7)).length]
      (some ⟨some (labels .seedReturn), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base (tape 7) (base (tape 7) ++ emittedBits q x z r)⟩ := by
  have hd (i j : Fin 8) (h : i ≠ j) : tape i ≠ tape j := fun e => h (distinct e)
  let w := (q + 1) * z + r
  let copied := Function.update base (tape 4) (encodeWord r)
  let computed := Function.update base (tape 4) (encodeWord w)
  let initialized := Function.update computed (tape 5) equalityBits
  let appended := Function.update initialized (tape 7)
    (base (tape 7) ++ emittedBits q x z r)
  let drained := Function.update appended (tape 4) []
  have copyRun : (advance (TM2.step program))^[2 * (r + 1) + 1]
      (some ⟨some (labels .seedReturn), (ambient, register), base⟩) =
      some ⟨some (labels .affine), (ambient, none), copied⟩ := by
    simpa only [copied, Nat.one_mul, Nat.add_zero, reverseEmpty, List.append_nil] using
      MachineUnaryAffineAt.seededAffineTrace (tape 2) (tape 3) (tape 4)
        (hd 2 3 (by decide)) (hd 2 4 (by decide)) (hd 3 4 (by decide)) 1 0
        (labels .seedReturn) (labels .copyReturn) (labels .restoreReturn)
        (some (labels .affine)) program (code .seedReturn) (code .copyReturn)
        (code .restoreReturn) base r [] (by simpa using returnWord) scratchEmpty ambient register
  have affineFrame (u : Nat) :
      MachineUnaryAffineAt.tapes (tape 1) (tape 3) (tape 4) base
        (encodeWord z ++ []) [] (encodeWord u ++ []) =
        Function.update base (tape 4) (encodeWord u) := by
    simp only [List.append_nil]
    rw [← targetWord, ← scratchEmpty]
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, Function.update_eq_self]
  have affineRun : (advance (TM2.step program))^[2 * (z + 1)]
      (some ⟨some (labels .affine), (ambient, none), copied⟩) =
      some ⟨some (labels .equality), (ambient, none), computed⟩ := by
    simpa only [affineFrame, copied, computed, w] using
      MachineUnaryAffineAt.affineTrace (tape 1) (tape 3) (tape 4)
        (hd 1 3 (by decide)) (hd 1 4 (by decide)) (hd 3 4 (by decide)) (q + 1)
        (labels .affine) (labels .restoreTarget) (some (labels .equality)) program
        (code .affine) (code .restoreTarget) base z r [] [] ambient none
  have initRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .equality), (ambient, none), computed⟩) =
      some ⟨some (labels (.row .relationRead)), (ambient, none), initialized⟩ := by
    change some (TM2.stepAux (program (labels .equality)) _ _) = _
    rw [code]
    simp [finishInstruction, stepAux_pushWord, TM2.stepAux, computed, initialized,
      hd 5 4 (by decide), equalityEmpty]
  have hfields : ∀ i, finishFields tape i ≠ tape 6 ∧ finishFields tape i ≠ tape 3 := by
    intro i
    fin_cases i <;> simp only []
    all_goals exact ⟨hd _ _ (by decide), hd _ _ (by decide)⟩
  have hbits : MachineTableRows.fieldBits (finishFields tape) initialized =
      emittedBits q x z r := by
    simp [MachineTableRows.fieldBits, initialized, computed, finishFields, tailWord,
      hd 0 4 (by decide), hd 0 5 (by decide), hd 4 5 (by decide), emittedBits, w]
  have hsize : MachineTableRows.fieldSize (finishFields tape) initialized =
      x + w + equalityBits.length + 2 := by
    rw [← MachineTableRows.fieldBits_length, hbits, emittedBits_length]
  have hout : initialized (tape 7) = base (tape 7) := by
    simp [initialized, computed, hd 7 4 (by decide), hd 7 5 (by decide)]
  have rowRun : (advance (TM2.step program))^[
      4 * (x + w + equalityBits.length + 2) + 2 * (base (tape 7)).length + 9]
      (some ⟨some (labels (.row .relationRead)), (ambient, none), initialized⟩) =
      some ⟨some (labels .clearReverse), (ambient, none), appended⟩ := by
    simpa only [hbits, hsize, hout, appended] using
      MachineTableRows.appendTrace (finishFields tape) (tape 6) (tape 7) (tape 3)
        hfields (hd 6 7 (by decide)) (hd 6 3 (by decide)) (hd 7 3 (by decide))
        (fun l => labels (.row l)) (some (labels .clearReverse)) program
        (fun l => code (.row l)) initialized
        (by simp [initialized, computed, hd 6 4 (by decide), hd 6 5 (by decide), rowEmpty])
        (by simp [initialized, computed, hd 3 4 (by decide), hd 3 5 (by decide), scratchEmpty])
        ambient none
  have hreverse : appended (tape 4) = encodeWord w := by
    simp [appended, initialized, computed, hd 4 7 (by decide), hd 4 5 (by decide)]
  have reverseRun : (advance (TM2.step program))^[w + 2]
      (some ⟨some (labels .clearReverse), (ambient, none), appended⟩) =
      some ⟨some (labels .clearEquality), (ambient, none), drained⟩ := by
    have h := MachineDrain.drainTrace (tape 4) (labels .clearReverse)
      (some (labels .clearEquality)) program (code .clearReverse)
      appended (appended (tape 4)) ambient none
    rw [Function.update_eq_self, hreverse, encodeWord_length] at h
    exact h
  have hequality : drained (tape 5) = equalityBits := by
    simp [drained, appended, initialized, hd 5 4 (by decide), hd 5 7 (by decide)]
  have finalFrame : Function.update drained (tape 5) [] =
      Function.update base (tape 7) (base (tape 7) ++ emittedBits q x z r) := by
    funext k
    by_cases h4 : k = tape 4
    · subst k
      simp [drained, hd 4 5 (by decide), hd 4 7 (by decide), reverseEmpty]
    · by_cases h5 : k = tape 5
      · subst k
        simp [hd 5 7 (by decide), equalityEmpty]
      · by_cases h7 : k = tape 7
        · subst k
          simp [drained, appended, h4, h5]
        · simp [drained, appended, initialized, computed, h4, h5, h7]
  have equalityRun : (advance (TM2.step program))^[equalityBits.length + 1]
      (some ⟨some (labels .clearEquality), (ambient, none), drained⟩) =
      some ⟨exit, (ambient, none),
        Function.update base (tape 7) (base (tape 7) ++ emittedBits q x z r)⟩ := by
    have h := MachineDrain.drainTrace (tape 5) (labels .clearEquality) exit program
      (code .clearEquality) drained (drained (tape 5)) ambient none
    rw [Function.update_eq_self, hequality, finalFrame] at h
    exact h
  exact joinTrace_inline_MachineRegularInternalRow (joinTrace_inline_MachineRegularInternalRow (joinTrace_inline_MachineRegularInternalRow (joinTrace_inline_MachineRegularInternalRow (joinTrace_inline_MachineRegularInternalRow
    copyRun affineRun) initRun) rowRun) reverseRun) equalityRun

inductive RotorLabel (q : Nat)
  | lookup (stage : MachineAffineLookup.Label)
  | initialize | divide | emit (r : Fin q)
  deriving DecidableEq, Fintype

def rotorLookupTapes (tape : Fin 8 → K) (j : Fin 5) : K :=
  tape ⟨j.val + 1, by omega⟩

omit [DecidableEq K] in
theorem rotorLookupTapes_injective (tape : Fin 8 → K) (h : Function.Injective tape) :
    Function.Injective (rotorLookupTapes tape) := by
  intro i j hij
  have hv := congrArg Fin.val (h hij)
  apply Fin.ext
  simpa only [Fin.val_mk, Nat.add_left_inj] using hv

omit [DecidableEq K] in
theorem rotorLookupTapes_outside (tape : Fin 8 → K) (h : Function.Injective tape)
    (i : Fin 5) : tape 0 ≠ rotorLookupTapes tape i := by
  intro he
  have hv := congrArg Fin.val (h he)
  change 0 = i.val + 1 at hv
  omega

def rotorInstruction (q : Nat) (positive : 0 < q) (p : Fin q)
    (tape : Fin 8 → K) (labels : RotorLabel q → Λ) (exit : Option Λ) :
    RotorLabel q → TM2.Stmt (Alphabet (K := K)) Λ (MachineFixedDivMod.State σ q)
  | .lookup stage => MachineAffineLookup.instruction (tape 0) (rotorLookupTapes tape)
      q p.val (fun l => labels (.lookup l)) (some (labels .initialize)) stage
  | .initialize => .push (tape 6) (fun _ => false)
      (.push (tape 7) (fun _ => false) (.goto fun _ => labels .divide))
  | .divide => MachineFixedDivMod.scanLoop q positive (tape 4) (tape 6)
      (labels .divide) (fun r => labels (.emit r))
  | .emit r => MachineFixedDivMod.emitter q positive (tape 7) exit r

def rotorFinalTapes {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q)
    (tape : Fin 8 → K) (base : K → List Bool) : K → List Bool :=
  MachineFixedDivMod.unaryTapes (tape 4) (tape 6) (tape 7)
    (MachineAffineLookup.finalTapes (rotorLookupTapes tape) base
      (ExpanderTableWords.rotationWords table) (q * i.val + p.val)
      (q * (ExpanderTables.lookup table (i, p)).1.val +
        (ExpanderTables.lookup table (i, p)).2.val))
    0 (ExpanderTables.lookup table (i, p)).1.val
      (ExpanderTables.lookup table (i, p)).2.val [] [] []

def rotorSteps {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) : Nat :=
  MachineAffineLookup.steps (ExpanderTableWords.rotationWords table) i.val q p.val +
    1 + (q * (ExpanderTables.lookup table (i, p)).1.val +
      (ExpanderTables.lookup table (i, p)).2.val + 2)

theorem rotorTrace {n q : Nat} (positive : 0 < q) (table : ExpanderTables.Table n q)
    (i : Fin n) (p : Fin q) (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : RotorLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (MachineFixedDivMod.State σ q))
    (code : ∀ l, program (labels l) = rotorInstruction q positive p tape labels exit l)
    (base : K → List Bool)
    (sourceWord : base (tape 0) = encodeWord i.val)
    (tableWord : base (tape 1) = encodeWords (ExpanderTableWords.rotationWords table))
    (flatEmpty : base (tape 4) = []) (scratchEmpty : base (tape 5) = [])
    (localEmpty : base (tape 6) = []) (returnEmpty : base (tape 7) = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[rotorSteps table i p]
      (some ⟨some (labels (.lookup .seed)),
        ((ambient, MachineFixedDivMod.residue q positive 0), register), base⟩) =
      some ⟨exit, ((ambient, MachineFixedDivMod.residue q positive 0), none),
        rotorFinalTapes table i p tape base⟩ := by
  have hd (a b : Fin 8) (h : a ≠ b) : tape a ≠ tape b := fun e => h (distinct e)
  let a := q * (ExpanderTables.lookup table (i, p)).1.val +
    (ExpanderTables.lookup table (i, p)).2.val
  let looked := MachineAffineLookup.finalTapes (rotorLookupTapes tape) base
    (ExpanderTableWords.rotationWords table) (q * i.val + p.val) a
  let initialized := Function.update (Function.update looked (tape 6) (encodeWord 0))
    (tape 7) (encodeWord 0)
  have lookupRun : (advance (TM2.step program))^[MachineAffineLookup.steps
      (ExpanderTableWords.rotationWords table) i.val q p.val]
      (some ⟨some (labels (.lookup .seed)),
        ((ambient, MachineFixedDivMod.residue q positive 0), register), base⟩) =
      some ⟨some (labels .initialize),
        ((ambient, MachineFixedDivMod.residue q positive 0), none), looked⟩ := by
    exact rotationLookupTrace table i p (tape 0) (rotorLookupTapes tape)
      (rotorLookupTapes_injective tape distinct) (rotorLookupTapes_outside tape distinct)
      (fun l => labels (.lookup l)) (some (labels .initialize)) program
      (fun l => code (.lookup l)) base tableWord scratchEmpty []
      (by simpa using sourceWord) (ambient, MachineFixedDivMod.residue q positive 0) register
  have lookedOther (k : Fin 8) (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) :
      looked (tape k) = base (tape k) := by
    exact MachineAffineLookup.finalTapes_other (rotorLookupTapes tape) base
      (ExpanderTableWords.rotationWords table) (q * i.val + p.val) a (tape k)
      (hd k 2 h2) (hd k 3 h3) (hd k 4 h4)
  have lookedFlat : looked (tape 4) = encodeWord a := by
    change MachineAffineLookup.finalTapes (rotorLookupTapes tape) base
      (ExpanderTableWords.rotationWords table) (q * i.val + p.val) a
      (rotorLookupTapes tape 3) = _
    rw [MachineAffineLookup.finalTapes_output]
    change encodeWord a ++ base (tape 4) = _
    rw [flatEmpty, List.append_nil]
  have initRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .initialize),
        ((ambient, MachineFixedDivMod.residue q positive 0), none), looked⟩) =
      some ⟨some (labels .divide),
        ((ambient, MachineFixedDivMod.residue q positive 0), none), initialized⟩ := by
    change some (TM2.stepAux (program (labels .initialize)) _ _) = _
    rw [code]
    simp [rotorInstruction, TM2.stepAux, initialized, encodeWord,
      lookedOther 6 (by decide) (by decide) (by decide),
      lookedOther 7 (by decide) (by decide) (by decide),
      hd 7 6 (by decide), localEmpty, returnEmpty]
  have initialFrame : MachineFixedDivMod.unaryTapes (tape 4) (tape 6) (tape 7)
      looked a 0 0 [] [] [] = initialized := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      MachineCopy.forkTapes, List.append_nil, ← lookedFlat, Function.update_eq_self,
      initialized]
  have finalFrame : MachineFixedDivMod.unaryTapes (tape 4) (tape 6) (tape 7)
      looked 0 (a / q) (a % q) [] [] [] = rotorFinalTapes table i p tape base := by
    dsimp only [a]
    rw [selected_rotation_div positive, selected_rotation_mod positive]
    rfl
  have divideRun : (advance (TM2.step program))^[a + 2]
      (some ⟨some (labels .divide),
        ((ambient, MachineFixedDivMod.residue q positive 0), none), initialized⟩) =
      some ⟨exit, ((ambient, MachineFixedDivMod.residue q positive 0), none),
        rotorFinalTapes table i p tape base⟩ := by
    simpa only [initialFrame, finalFrame] using
      MachineFixedDivMod.divModTrace q positive (tape 4) (tape 6) (tape 7)
        (hd 4 6 (by decide)) (hd 4 7 (by decide)) (hd 6 7 (by decide))
        (labels .divide) (fun r => labels (.emit r)) exit program (code .divide)
        (fun r => code (.emit r)) looked a [] [] [] ambient none
  exact joinTrace_inline_MachineRegularInternalRow (joinTrace_inline_MachineRegularInternalRow lookupRun initRun) divideRun

theorem rotorSteps_le {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) :
    rotorSteps table i p ≤ 2 * i.val +
      5 * (encodeWords (ExpanderTableWords.rotationWords table)).length + n * q + 8 := by
  have hl := MachineAffineLookup.steps_le (ExpanderTableWords.rotationWords table)
    i.val q p.val _ (selected_rotation table i p)
  have hb := (ExpanderTables.rowIndex n q (ExpanderTables.lookup table (i, p))).isLt
  rw [ExpanderTables.rowIndex_val] at hb
  unfold rotorSteps
  omega

inductive SelectExtraTape
  | localIndex | owner | cloudSize | prefixOffset | darts
  | savedLeft | savedRight | localWork | sizeWork
  deriving DecidableEq

instance : Fintype SelectExtraTape := derive_fintype% SelectExtraTape

abbrev SelectTape := MachineCloudSelect.Tape ⊕ SelectExtraTape
abbrev RawSelectAlphabet : SelectTape → Type :=
  MachineEmbedding.Alphabet MachineCloudSelect.Alphabet (fun _ : SelectExtraTape => Bool)
abbrev SelectAlphabet (_ : SelectTape) := Bool

theorem selectAlphabet_eq : RawSelectAlphabet = SelectAlphabet := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => rfl

def selectToBoolWord : (k : SelectTape) → List (RawSelectAlphabet k) → List Bool
  | .inl (.inl _), word => word
  | .inl (.inr _), word => word
  | .inr _, word => word

def selectToBoolTapes (base : ∀ k, List (RawSelectAlphabet k)) : SelectTape → List Bool :=
  fun k => selectToBoolWord k (base k)

private theorem alphabet_tapes_apply_inline_MachineRegularInternalRow {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : ∀ k, List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

theorem selectToBoolTapes_eq (base : ∀ k, List (RawSelectAlphabet k)) :
    selectToBoolTapes base = MachineAlphabetTransport.tapes selectAlphabet_eq base := by
  funext k
  rw [alphabet_tapes_apply_inline_MachineRegularInternalRow]
  cases k with
  | inl k => cases k <;> rfl
  | inr k => rfl

abbrev SelectState (σ : Type) := MachineUnaryLessAt.State (σ × MachineCloudSelect.Phase)

def selectStateEquiv (σ : Type) : (MachineCloudSelect.State σ × Unit) ≃ SelectState σ where
  toFun s := (((s.1.1.1.1, s.1.2), s.1.1.1.2), s.1.1.2)
  invFun s := ((((s.1.1.1, s.1.2), s.2), s.1.1.2), ())
  left_inv s := by rcases s with ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, ⟨⟩⟩; rfl
  right_inv s := by rcases s with ⟨⟨⟨a, b⟩, c⟩, d⟩; rfl

def selectScratch : SelectTape := .inl (.inl .scratch)
def selectQuery : SelectTape := .inl (.inl .target)
def selectOutput : SelectTape := .inl (.inr ())

def compareSlots : Fin 4 ↪ SelectTape where
  toFun i := ![.inr .localIndex, .inr .cloudSize, .inr .savedLeft, .inr .savedRight] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def subtractSlots : Fin 4 ↪ SelectTape where
  toFun i := ![.inr .localWork, .inr .sizeWork, .inr .savedLeft, .inr .savedRight] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

inductive SelectCopy
  | oldLocal | oldOwner | dummyLocal | dummySize | dummyDifference
  deriving DecidableEq

instance : Fintype SelectCopy := derive_fintype% SelectCopy

inductive SelectAdd
  | prefixOffset | darts
  deriving DecidableEq

instance : Fintype SelectAdd := derive_fintype% SelectAdd

inductive SelectAddStage | scan | restore
  deriving DecidableEq

instance : Fintype SelectAddStage := derive_fintype% SelectAddStage

inductive SelectControl
  | compare (stage : MachineUnaryLessAt.Label)
  | choose
  | copy (kind : SelectCopy) (stage : MachineUnaryAffineAt.Label)
  | subtract
  | add (kind : SelectAdd) (stage : SelectAddStage)
  | cleanup (i : Fin 5)
  deriving DecidableEq, Fintype

abbrev SelectLabel := MachineCloudSelect.Label ⊕ SelectControl

def copySource : SelectCopy → SelectTape
  | .oldLocal | .dummyLocal => .inr .localIndex
  | .oldOwner => .inr .owner
  | .dummySize => .inr .cloudSize
  | .dummyDifference => .inr .localWork

def copyDestination : SelectCopy → SelectTape
  | .oldLocal | .oldOwner => selectQuery
  | .dummyLocal => .inr .localWork
  | .dummySize => .inr .sizeWork
  | .dummyDifference => selectOutput

def afterCopy : SelectCopy → SelectLabel
  | .oldLocal => .inr (.copy .oldOwner .seed)
  | .oldOwner => .inl (.inr .initialize)
  | .dummyLocal => .inr (.copy .dummySize .seed)
  | .dummySize => .inr .subtract
  | .dummyDifference => .inr (.add .prefixOffset .scan)

def addSource : SelectAdd → SelectTape
  | .prefixOffset => .inr .prefixOffset
  | .darts => .inr .darts

def afterAdd : SelectAdd → SelectLabel
  | .prefixOffset => .inr (.add .darts .scan)
  | .darts => .inr (.cleanup 0)

def cleanupTape (i : Fin 5) : SelectTape :=
  ![selectQuery, .inr .localWork, .inr .sizeWork, .inr .savedLeft, .inr .savedRight] i

def afterCleanup (i : Fin 5) : Option SelectLabel :=
  if h : i.val + 1 < 5 then some (.inr (.cleanup ⟨i.val + 1, h⟩)) else none

def selectControl : SelectControl → TM2.Stmt SelectAlphabet SelectLabel (SelectState σ)
  | .compare stage => MachineUnaryLessAt.statement compareSlots
      (fun s => .inr (.compare s)) (some (.inr .choose)) stage
  | .choose => .branch (fun s => s.1.2)
      (.load (fun s => ((s.1.1, false), none))
        (.goto fun _ => .inr (.copy .oldLocal .seed)))
      (.load (fun s => ((s.1.1, false), none))
        (.goto fun _ => .inr (.copy .dummyLocal .seed)))
  | .copy kind .seed => MachineUnaryAffineAt.seed (copyDestination kind) 0
      (.inr (.copy kind .scan))
  | .copy kind .scan => MachineUnaryAffineAt.scan (copySource kind) selectScratch
      (copyDestination kind) 1 (.inr (.copy kind .scan)) (.inr (.copy kind .restore))
  | .copy kind .restore => Reduction.MachineTransfer.loopAt selectScratch (copySource kind)
      id false (.inr (.copy kind .restore)) (some (afterCopy kind))
  | .subtract => MachineUnaryLessAt.scan subtractSlots (.inr .subtract)
      (.inr (.copy .dummyDifference .seed))
  | .add kind .scan => MachineUnaryAffineAt.scan (addSource kind) selectScratch selectOutput 1
      (.inr (.add kind .scan)) (.inr (.add kind .restore))
  | .add kind .restore => Reduction.MachineTransfer.loopAt selectScratch (addSource kind)
      id false (.inr (.add kind .restore)) (some (afterAdd kind))
  | .cleanup i => MachineDrain.drain (cleanupTape i) (.inr (.cleanup i)) (afterCleanup i)

def rawSelectProgram : SelectLabel → TM2.Stmt RawSelectAlphabet SelectLabel (SelectState σ) :=
  MachineStateEquiv.program (selectStateEquiv σ)
    (MachineEmbedding.program (some (.inr (.cleanup 0))) MachineCloudSelect.program
      (fun control => MachineStateEquiv.statement (selectStateEquiv σ).symm
        (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl control))))

def selectProgram : SelectLabel → TM2.Stmt SelectAlphabet SelectLabel (SelectState σ) :=
  MachineAlphabetTransport.program selectAlphabet_eq rawSelectProgram

@[simp] theorem selectProgram_control (l : SelectControl) :
    selectProgram (σ := σ) (.inr l) = selectControl l := by
  change MachineAlphabetTransport.statement selectAlphabet_eq
    (MachineStateEquiv.statement (selectStateEquiv σ)
      (MachineStateEquiv.statement (selectStateEquiv σ).symm
        (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl l)))) = _
  have h := MachineStateEquiv.statement_symm_statement (selectStateEquiv σ).symm
    (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl (σ := σ) l))
  simp only [Equiv.symm_symm] at h
  rw [h]
  exact MachineAlphabetTransport.statement_roundtrip selectAlphabet_eq _

def selectCleanState (ambient : σ) (register : Option Bool) : SelectState σ :=
  (((ambient, .checking), false), register)

theorem selectComparisonTrace (base : SelectTape → List Bool) (j k : Nat)
    (hj : base (.inr .localIndex) = encodeWord j)
    (hk : base (.inr .cloudSize) = encodeWord k)
    (hl : base (.inr .savedLeft) = []) (hr : base (.inr .savedRight) = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[MachineUnaryLessAt.steps j k + 1]
      (some ⟨some (.inr (.compare .scan)), selectCleanState ambient register, base⟩) =
      some ⟨some (.inr (.copy (if j < k then .oldLocal else .dummyLocal) .seed)),
        selectCleanState ambient none, base⟩ := by
  have h := MachineUnaryLessAt.lessThanTrace compareSlots
    (fun l => .inr (.compare l)) (some (.inr .choose)) selectProgram
    (fun l => by rw [selectProgram_control]; rfl)
    base j k [] [] (by change base (.inr .localIndex) = _; simpa only [List.append_nil] using hj)
    (by change base (.inr .cloudSize) = _; simpa only [List.append_nil] using hk) hl hr
    (ambient, MachineCloudSelect.Phase.checking) false register
  simp only [selectCleanState]
  rw [Function.iterate_succ_apply', h, advance_some]
  change some (TM2.stepAux (selectProgram (.inr .choose)) _ _) = _
  rw [selectProgram_control]
  by_cases hlt : j < k <;> simp [selectControl, TM2.stepAux, hlt]

theorem selectCopyTrace (kind : SelectCopy) (base : SelectTape → List Bool)
    (a : Nat) (hword : base (copySource kind) = encodeWord a)
    (hscratch : base selectScratch = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[2 * (a + 1) + 1]
      (some ⟨some (.inr (.copy kind .seed)), selectCleanState ambient register, base⟩) =
      some ⟨some (afterCopy kind), selectCleanState ambient none,
        Function.update base (copyDestination kind)
          (encodeWord a ++ base (copyDestination kind))⟩ := by
  have h₁ : copySource kind ≠ selectScratch := by cases kind <;> decide
  have h₂ : copySource kind ≠ copyDestination kind := by cases kind <;> decide
  have h₃ : selectScratch ≠ copyDestination kind := by cases kind <;> decide
  simpa only [Nat.one_mul, Nat.add_zero, selectCleanState] using
    MachineUnaryAffineAt.seededAffineTrace (copySource kind) selectScratch (copyDestination kind)
      h₁ h₂ h₃ 1 0 (.inr (.copy kind .seed)) (.inr (.copy kind .scan))
      (.inr (.copy kind .restore)) (some (afterCopy kind)) selectProgram
      (by rw [selectProgram_control]; rfl) (by rw [selectProgram_control]; rfl)
      (by rw [selectProgram_control]; rfl) base a [] (by simpa using hword) hscratch
      ((ambient, MachineCloudSelect.Phase.checking), false) register

theorem selectAddTrace (kind : SelectAdd) (base : SelectTape → List Bool)
    (a b : Nat) (hword : base (addSource kind) = encodeWord a)
    (houtput : base selectOutput = encodeWord b) (hscratch : base selectScratch = [])
    (ambient : σ) :
    (advance (TM2.step selectProgram))^[2 * (a + 1)]
      (some ⟨some (.inr (.add kind .scan)), selectCleanState ambient none, base⟩) =
      some ⟨some (afterAdd kind), selectCleanState ambient none,
        Function.update base selectOutput (encodeWord (a + b))⟩ := by
  have h₁ : addSource kind ≠ selectScratch := by cases kind <;> decide
  have h₂ : addSource kind ≠ selectOutput := by cases kind <;> decide
  have h₃ : selectScratch ≠ selectOutput := by decide
  have frame (n : Nat) : MachineUnaryAffineAt.tapes (addSource kind) selectScratch selectOutput
      base (encodeWord a ++ []) [] (encodeWord n ++ []) =
        Function.update base selectOutput (encodeWord n) := by
    simp only [List.append_nil]
    rw [← hword, ← hscratch]
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, Function.update_eq_self]
  have h := MachineUnaryAffineAt.affineTrace (addSource kind) selectScratch selectOutput
    h₁ h₂ h₃ 1 (.inr (.add kind .scan)) (.inr (.add kind .restore))
    (some (afterAdd kind)) selectProgram
    (by rw [selectProgram_control]; rfl) (by rw [selectProgram_control]; rfl)
    base a b [] [] ((ambient, MachineCloudSelect.Phase.checking), false) none
  rw [frame, frame] at h
  rw [← houtput, Function.update_eq_self] at h
  simpa only [Nat.one_mul, selectCleanState] using h

abbrev CoreTape := Fin 27
abbrev CoreState (σ : Type) (q : Nat) :=
  (σ × (MachineFixedBlockMap.Buffer 4096 ×
    (Fin q × (Bool × MachineCloudSelect.Phase)))) × Option Bool

inductive CoreLabel (q : Nat)
  | rotor (stage : RotorLabel q)
  | select (stage : SelectLabel)
  | finish (stage : FinishLabel)
  | cleanup (i : Fin 10)
  deriving DecidableEq, Fintype

def coreEntry (q : Nat) : CoreLabel q := .rotor (.lookup .seed)

theorem selectCloudTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v))
    (extra : SelectExtraTape → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[MachineCloudSelect.cloudSelectSteps t v i []]
      (some ⟨some (.inl (.inr .initialize)), selectCleanState ambient register,
        selectToBoolTapes (MachineEmbedding.tapes
          (MachineCloudSelect.memory (GraphTables.tableBits t) []
            (MachineCloudSelect.queryWord v.val i.val []) [] [] [] []) extra)⟩) =
      some ⟨some (.inr (.cleanup 0)), selectCleanState ambient none,
        selectToBoolTapes (MachineEmbedding.tapes
          (MachineCloudSelect.memory (GraphTables.tableBits t) []
            (MachineCloudSelect.queryWord v.val i.val []) [] [] []
            (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val)) extra)⟩ := by
  let source := MachineCloudSelect.program (σ := σ)
  let more := fun c => MachineStateEquiv.statement (selectStateEquiv σ).symm
    (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl (σ := σ) c))
  let caller := MachineEmbedding.program (some (.inr (.cleanup 0))) source more
  let embed := MachineEmbedding.configuration (K := MachineCloudSelect.Tape)
    (Γ := MachineCloudSelect.Alphabet) (σ := MachineCloudSelect.State σ)
    (some (Sum.inr (SelectControl.cleanup 0)) : Option SelectLabel) () extra
  have sourceRun := MachineCloudSelect.cloudSelectTrace t v i [] [] ambient register
  have lifted := liftSuccessfulTrace (TM2.step source) (TM2.step caller) embed
    (MachineEmbedding.step_simulation (some (.inr (.cleanup 0))) () extra source more)
    _ _ _ sourceRun
  have transported := MachineStateEquiv.trace (selectStateEquiv σ) caller _ _ _ lifted
  have boolean := MachineAlphabetTransport.successfulTrace selectAlphabet_eq
    (MachineStateEquiv.program (selectStateEquiv σ) caller) _ _ _ transported
  simp only [embed, MachineCloudSelect.cfg, MachineStateEquiv.configuration, MachineEmbedding.configuration,
    MachineEmbedding.label, selectStateEquiv, List.append_nil,
    MachineAlphabetTransport.configuration_mk, ← selectToBoolTapes_eq] at boolean
  convert boolean using 1 <;> rfl

def selectExtraMemory (j v k offset m : Nat)
    (savedLeft savedRight localWork sizeWork : List Bool) :
    SelectExtraTape → List Bool
  | .localIndex => encodeWord j
  | .owner => encodeWord v
  | .cloudSize => encodeWord k
  | .prefixOffset => encodeWord offset
  | .darts => encodeWord m
  | .savedLeft => savedLeft
  | .savedRight => savedRight
  | .localWork => localWork
  | .sizeWork => sizeWork

def selectMemory (graph : List Bool) (j v k offset m : Nat)
    (query output savedLeft savedRight localWork sizeWork : List Bool) :
    SelectTape → List Bool :=
  selectToBoolTapes (MachineEmbedding.tapes
    (MachineCloudSelect.memory graph [] query [] [] [] output)
    (selectExtraMemory j v k offset m savedLeft savedRight localWork sizeWork))

@[simp] theorem selectMemory_query (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectQuery = query := rfl

@[simp] theorem selectMemory_output (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectOutput = output := rfl

@[simp] theorem selectMemory_scratch (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectScratch = [] := rfl

@[simp] theorem selectMemory_extra (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) (z : SelectExtraTape) :
    selectMemory graph j v k o m query output a b c d (.inr z) =
      selectExtraMemory j v k o m a b c d z := rfl

@[simp] theorem update_selectMemory_query (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) selectQuery word =
      selectMemory graph j v k o m word output a b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_output (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) selectOutput word =
      selectMemory graph j v k o m query word a b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_local (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .localWork) word =
      selectMemory graph j v k o m query output a b word d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_size (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .sizeWork) word =
      selectMemory graph j v k o m query output a b c word := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_left (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .savedLeft) word =
      selectMemory graph j v k o m query output word b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_right (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .savedRight) word =
      selectMemory graph j v k o m query output a word c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

theorem selectCleanupTrace (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) (ambient : σ) :
    (advance (TM2.step selectProgram))^[query.length + c.length + d.length + a.length + b.length + 5]
      (some ⟨some (.inr (.cleanup 0)), selectCleanState ambient none,
        selectMemory graph j v k o m query output a b c d⟩) =
      some ⟨none, selectCleanState ambient none,
        selectMemory graph j v k o m [] output [] [] [] []⟩ := by
  have h0 := MachineDrain.drainTrace selectQuery (.inr (.cleanup 0))
    (some (.inr (.cleanup 1))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m query output a b c d) query
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_query] at h0
  have h1 := MachineDrain.drainTrace (.inr .localWork) (.inr (.cleanup 1))
    (some (.inr (.cleanup 2))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output a b c d) c
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_local] at h1
  have h2 := MachineDrain.drainTrace (.inr .sizeWork) (.inr (.cleanup 2))
    (some (.inr (.cleanup 3))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output a b [] d) d
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_size] at h2
  have h3 := MachineDrain.drainTrace (.inr .savedLeft) (.inr (.cleanup 3))
    (some (.inr (.cleanup 4))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output a b [] []) a
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_left] at h3
  have h4 := MachineDrain.drainTrace (.inr .savedRight) (.inr (.cleanup 4))
    none selectProgram (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output [] b [] []) b
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_right] at h4
  have total := joinTrace_inline_MachineRegularInternalRow (joinTrace_inline_MachineRegularInternalRow (joinTrace_inline_MachineRegularInternalRow (joinTrace_inline_MachineRegularInternalRow h0 h1) h2) h3) h4
  have hn : query.length + c.length + d.length + a.length + b.length + 5 =
      ((((query.length + 1) + (c.length + 1)) + (d.length + 1)) + (a.length + 1)) +
        (b.length + 1) := by omega
  rw [hn]
  exact total

def oldSelectSteps (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) : Nat :=
  (2 * (i.val + 1) + 1) + (2 * (v.val + 1) + 1) +
    MachineCloudSelect.cloudSelectSteps t v i [] + (v.val + i.val + 7)

theorem selectOldTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (o : Nat) (ambient : σ) :
    (advance (TM2.step selectProgram))^[oldSelectSteps t v i]
      (some ⟨some (.inr (.copy .oldLocal .seed)), selectCleanState ambient none,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v) o t.darts [] [] [] [] [] []⟩) =
      some ⟨none, selectCleanState ambient none,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v) o t.darts []
          (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val) [] [] [] []⟩ := by
  let graph := GraphTables.tableBits t
  let k := PreprocessingCloudIndex.cloudSize t v
  have hi := selectCopyTrace .oldLocal
    (selectMemory graph i.val v.val k o t.darts [] [] [] [] [] [])
    i.val rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_query, update_selectMemory_query, List.append_nil] at hi
  have hv := selectCopyTrace .oldOwner
    (selectMemory graph i.val v.val k o t.darts (encodeWord i.val) [] [] [] [] [])
    v.val rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_query, update_selectMemory_query] at hv
  have hc := selectCloudTrace t v i (selectExtraMemory i.val v.val k o t.darts [] [] [] [])
    ambient none
  have hq : MachineCloudSelect.queryWord v.val i.val [] =
      encodeWord v.val ++ encodeWord i.val := by
    simp only [MachineCloudSelect.queryWord, MachineCloudRank.queryWord, List.append_nil]
  change (advance (TM2.step selectProgram))^[MachineCloudSelect.cloudSelectSteps t v i []]
    (some ⟨some (.inl (.inr .initialize)), selectCleanState ambient none,
      selectMemory graph i.val v.val k o t.darts
        (MachineCloudSelect.queryWord v.val i.val []) [] [] [] [] []⟩) =
    some ⟨some (.inr (.cleanup 0)), selectCleanState ambient none,
      selectMemory graph i.val v.val k o t.darts
        (MachineCloudSelect.queryWord v.val i.val [])
        (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val) [] [] [] []⟩ at hc
  rw [hq] at hc
  have hd := selectCleanupTrace graph i.val v.val k o t.darts
    (encodeWord v.val ++ encodeWord i.val)
    (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val) [] [] [] [] ambient
  have hn : (encodeWord v.val ++ encodeWord i.val).length + ([] : List Bool).length + ([] : List Bool).length +
      ([] : List Bool).length + ([] : List Bool).length + 5 = v.val + i.val + 7 := by
    simp only [List.length_append, encodeWord_length, List.length_nil]
    omega
  rw [hn] at hd
  exact joinTrace_inline_MachineRegularInternalRow (joinTrace_inline_MachineRegularInternalRow (joinTrace_inline_MachineRegularInternalRow hi hv) hc) hd

end DFVSGames.Foundations.Complexity.MachineRegularInternalRow
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
