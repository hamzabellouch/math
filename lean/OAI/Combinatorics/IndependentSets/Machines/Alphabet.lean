import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineAffineLookup
import OAI.Combinatorics.IndependentSets.Machines.MachineTableRows
import OAI.Combinatorics.IndependentSets.Expansion.ExpanderTableWords
import OAI.Combinatorics.IndependentSets.Machines.MachineFixedDivMod
import OAI.Combinatorics.IndependentSets.Machines.MachineCloudSelect
import OAI.Combinatorics.IndependentSets.Expansion.PreprocessingInternalRows

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow

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

theorem selected_rotation_mod {n q : Nat} (positive : 0 < q)
    (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) :
    (q * (ExpanderTables.lookup table (i, p)).1.val +
      (ExpanderTables.lookup table (i, p)).2.val) % q =
        (ExpanderTables.lookup table (i, p)).2.val := by
  obtain ⟨degree, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
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

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
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
    fin_cases i
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
  exact joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
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
  exact joinTrace (joinTrace lookupRun initRun) divideRun

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

instance : Fintype SelectExtraTape where
  elems := {.localIndex, .owner, .cloudSize, .prefixOffset, .darts, .savedLeft, .savedRight,
    .localWork, .sizeWork}
  complete value := by cases value <;> simp

abbrev SelectTape := MachineCloudSelect.Tape ⊕ SelectExtraTape
abbrev RawSelectAlphabet : SelectTape → Type :=
  MachineEmbedding.Alphabet MachineCloudSelect.Alphabet (fun _ : SelectExtraTape => Bool)

end IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow

end OAI
