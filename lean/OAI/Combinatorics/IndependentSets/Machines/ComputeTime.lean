import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineRegularOwnerProgram
import OAI.Combinatorics.IndependentSets.Machines.Machine2
import OAI.Combinatorics.IndependentSets.Machines.Basic

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularTable
open Turing MachineComposition
open IndependentSetsGames.Foundations.PCP
namespace Header
variable {σ : Type}

theorem prefixTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[MachineCloudPrefix.totalTime t t.vertices []]
      (some ⟨some (.prefix .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩) =
      some ⟨some (.copyFirst .count), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
          [] [] [] [] [] [] output⟩ := by
  have h := MachineCloudPadding.Placement.trace Sum.inl prefixView prefixView_left prefixView_right
    Label.prefix (some (Label.copyFirst .count))
    (frame [] [] [] [] [] (encodeWord t.darts) [] [] [] [] [] [] output)
    (MachineCloudPrefix.program (σ := σ)) (program q) (fun _ => rfl) _ _ _
    (MachineCloudPrefix.prefixTrace t t.vertices (Nat.le_refl _) [] ambient register)
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    prefixTapes, frame_m, frame_index, frame_work, frame_scratch, frame_vertices, frame_darts,
    frame_emit, frame_output, List.append_nil, paddingTotal, frame, memory,
    mTape, indexTape, workTape, scratchTape, verticesTape, dartsTape, emitTape, outputTape] using h

def computeTime (t : GraphTables.Table) : Nat :=
  (2 * (t.darts + 2) + (paddingTotal t + 1)) + (2 * (vertexTotal t + 1) + 1)

theorem computeTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[computeTime t]
      (some ⟨some (.copyFirst .count), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
          [] [] [] [] [] [] output⟩) =
      some ⟨some (.copyFirst .rEmit), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output⟩ := by
  have hc := MachineCopy.copyTrace mTape verticesTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .count) (Label.copySecond .count) (some Label.add)
    (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
      [] [] [] [] [] [] output) rfl (ambient, false) register
  simp only [frame_m, frame_vertices, encodeWord_length, List.append_nil, update_frame_vertices] at hc
  have ha := MachineUnaryAddAt.addFromTapes sumTape verticesTape (by decide)
    Label.add (some Label.scaleSeed) (program q) rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
      [] [] [] (encodeWord t.darts) [] [] output)
    (paddingTotal t) t.darts [] [] (by simp) (by simp) (ambient, false) none
  simp only [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
    List.append_nil, update_frame_sum, update_frame_vertices] at ha
  rw [show paddingTotal t + t.darts = vertexTotal t by rw [vertexTotal_eq]; omega] at ha
  have hm := MachineUnaryAffineAt.seededAffineTrace verticesTape scratchTape dartsTape
    (by decide) (by decide) (by decide) (q + 1) 0 Label.scaleSeed Label.scaleScan
    Label.scaleRestore (some (Label.copyFirst .rEmit)) (program q) rfl rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
      [] [] [] (encodeWord (vertexTotal t)) [] [] output)
    (vertexTotal t) [] (by simp) rfl (ambient, false) none
  simp only [frame_darts, List.append_nil, Nat.add_zero, update_frame_darts] at hm
  rw [show (q + 1) * vertexTotal t = dartTotal q t by unfold dartTotal; ac_rfl] at hm
  exact appendTrace _ (appendTrace _ hc ha) hm

def headerBits (q : Nat) (t : GraphTables.Table) : List Bool :=
  encodeWords [vertexTotal t, dartTotal q t]

theorem headerBits_eq (q : Nat) (t : GraphTables.Table) :
    headerBits q t = encodeWord (vertexTotal t) ++ encodeWord (dartTotal q t) := by
  simp only [headerBits, encodeWords, List.append_nil]

theorem headerBits_length (q : Nat) (t : GraphTables.Table) :
    (headerBits q t).length = vertexTotal t + dartTotal q t + 2 := by
  rw [headerBits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem cleanupZerosStep (q : Nat) (table n m N R output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .cleanupZeros, ((ambient, false), register),
        frame table n n (encodeWord 0) (encodeWord 0) m [] [] [] N R [] output⟩ =
      some ⟨some .clearQuery, ((ambient, false), none),
        frame table n n [] [] m [] [] [] N R [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

def emitTime (q : Nat) (t : GraphTables.Table) (output : List Bool) : Nat :=
  (((2 * (dartTotal q t + 2) + 2 * (vertexTotal t + 2)) +
    (2 * ((headerBits q t).length + output.length) + 3)) + 1) + (t.vertices + 1) + 1

theorem emitTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[emitTime q t output]
      (some ⟨some (.copyFirst .rEmit), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ := by
  have hr := MachineCopy.copyTrace dartsTape emitTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .rEmit) (Label.copySecond .rEmit)
    (some (Label.copyFirst .nEmit)) (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output)
    rfl (ambient, false) register
  simp only [frame_darts, frame_emit, encodeWord_length, List.append_nil, update_frame_emit] at hr
  have hn := MachineCopy.copyTrace verticesTape emitTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .nEmit) (Label.copySecond .nEmit)
    (some Label.appendFirst) (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) (encodeWord (dartTotal q t)) output)
    rfl (ambient, false) none
  simp only [frame_vertices, frame_emit, encodeWord_length, update_frame_emit, ← headerBits_eq] at hn
  have ha := MachineAppendAt.appendTrace emitTape outputTape scratchTape
    (by decide) (by decide) (by decide) false Label.appendFirst Label.appendSecond Label.appendThird
    (some Label.cleanupZeros) (program q) rfl rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) (headerBits q t) output)
    rfl (ambient, false) none
  simp only [frame_emit, frame_output, MachineAppendAt.appendTapes,
    Reduction.MachineTransfer.tapesAt, update_frame_emit, update_frame_output] at ha
  have hz : (advance (TM2.step (program q)))^[1]
      (some ⟨some .cleanupZeros, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
          (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] (output ++ headerBits q t)⟩) =
      some ⟨some .clearQuery, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          [] [] (encodeWord t.darts) [] [] [] (encodeWord (vertexTotal t))
          (encodeWord (dartTotal q t)) [] (output ++ headerBits q t)⟩ :=
    cleanupZerosStep q _ _ _ _ _ _ ambient none
  have hc := MachineLookup.discardTrace queryTape Label.clearQuery Label.done (program q) rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      [] [] (encodeWord t.darts) [] [] [] (encodeWord (vertexTotal t))
      (encodeWord (dartTotal q t)) [] (output ++ headerBits q t))
    t.vertices [] (by simp) (ambient, false) none
  simp only [update_frame_query] at hc
  have hd : (advance (TM2.step (program q)))^[1]
      (some ⟨some .done, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ := rfl
  exact appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ hr hn) ha) hz) hc) hd

def totalTime (q : Nat) (t : GraphTables.Table) (output : List Bool) : Nat :=
  ((readTime t + MachineCloudPrefix.totalTime t t.vertices []) + computeTime t) + emitTime q t output

theorem trace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[totalTime q t output]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ :=
  appendTrace _ (appendTrace _ (appendTrace _ (readTrace q t output ambient register)
    (prefixTrace q t output ambient none)) (computeTrace q t output ambient none))
      (emitTrace q t output ambient none)

noncomputable def arithmeticPolynomial (q : Nat) : Polynomial Nat :=
  let X : Polynomial Nat := Polynomial.X
  let G : Polynomial Nat := Polynomial.C ExpanderFamily.growth * X
  let D : Polynomial Nat := Polynomial.C (ExpanderFamily.growth * (q + 1)) * X
  (12 * X + 11) + ((2 * (X + 2) + (G + 1)) + (2 * (G + 1) + 1)) +
    (((2 * (D + 2) + 2 * (G + 2)) + (2 * ((G + D + 2) + X) + 3)) + 1 + (X + 1) + 1)

noncomputable def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineCloudPrefix.timePolynomial.comp (2 * Polynomial.X + 1) + arithmeticPolynomial q

theorem totalTime_le (q : Nat) (t : GraphTables.Table) (output : List Bool) :
    totalTime q t output ≤ (timePolynomial q).eval ((GraphTables.tableBits t).length + output.length) := by
  let L := (GraphTables.tableBits t).length + output.length
  have hT : (GraphTables.tableBits t).length ≤ L := by unfold L; omega
  have hO : output.length ≤ L := by unfold L; omega
  have hn := (GraphTables.vertices_le_tableBits_length t).trans hT
  have hm := (GraphTables.darts_le_tableBits_length t).trans hT
  have hN : vertexTotal t ≤ ExpanderFamily.growth * L :=
    (PreprocessingMachineBounds.regularVertices_le_input t).trans
      (Nat.mul_le_mul_left ExpanderFamily.growth hT)
  have hS : paddingTotal t ≤ ExpanderFamily.growth * L :=
    (PreprocessingMachineBounds.prefix_le_input t t.vertices).trans
      (Nat.mul_le_mul_left ExpanderFamily.growth hT)
  have hR : dartTotal q t ≤ (ExpanderFamily.growth * (q + 1)) * L := by
    calc
      _ ≤ (ExpanderFamily.growth * L) * (q + 1) := Nat.mul_le_mul_right (q + 1) hN
      _ = _ := by ac_rfl
  have hr0 := MachinePreservingLookupClean.steps_le (GraphTables.tableWords t) 0 t.vertices
    (by simp [GraphTables.tableWords])
  have hr1 := MachinePreservingLookupClean.steps_le (GraphTables.tableWords t) 1 t.darts
    (by simp [GraphTables.tableWords])
  have hread : readTime t ≤ 12 * L + 11 := by
    change _ ≤ 6 * (GraphTables.tableBits t).length + 4 at hr0 hr1
    unfold readTime
    omega
  have hprefixInput : MachineCloudPrefix.inputLength t t.vertices [] ≤ 2 * L + 1 := by
    simp only [MachineCloudPrefix.inputLength, List.append_nil, encodeWord_length]
    omega
  have hp := (MachineCloudPrefix.totalTime_le t t.vertices (Nat.le_refl _) []).trans
    (natPolynomial_eval_mono MachineCloudPrefix.timePolynomial hprefixInput)
  have harith : readTime t + computeTime t + emitTime q t output ≤
      (arithmeticPolynomial q).eval L := by
    simp only [arithmeticPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
    unfold computeTime emitTime
    rw [headerBits_length]
    omega
  have htotal := Nat.add_le_add hp harith
  simpa only [totalTime, timePolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one,
    L, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal

def inTime (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩
      (some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩)
      ((timePolynomial q).eval ((GraphTables.tableBits t).length + output.length)) where
  steps := totalTime q t output
  evals_in_steps := trace q t output ambient register
  steps_le_m := totalTime_le q t output

end Header

namespace Fuel

variable {K Λ σ : Type} [DecidableEq K]

def guard (fuel : K) (body : Λ) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  .pop fuel (fun s bit => (s.1, bit))
    (.branch (fun s => s.2.getD false)
      (.load (fun s => (s.1, none)) (.goto fun _ => body))
      (.load (fun s => (s.1, none))
        (match exit with | some label => .goto fun _ => label | none => .halt)))

theorem guard_succ (fuel : K) (body : Λ) (exit : Option Λ)
    (base : K → List Bool) (n : Nat) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (guard fuel body exit) (ambient, register)
      (Function.update base fuel (encodeWord (n + 1))) =
      ⟨some body, (ambient, none), Function.update base fuel (encodeWord n)⟩ := by
  simp [guard, TM2.stepAux, encodeWord, List.replicate_succ]

theorem guard_zero (fuel : K) (body : Λ) (exit : Option Λ)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (guard fuel body exit) (ambient, register)
      (Function.update base fuel (encodeWord 0)) =
      ⟨exit, (ambient, none), Function.update base fuel []⟩ := by
  cases exit <;> simp [guard, TM2.stepAux, encodeWord]

def increment (counter : K) (next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  .push counter (fun _ => true) (.goto fun _ => next)

theorem increment_step (counter : K) (next : Λ) (base : K → List Bool)
    (n : Nat) (state : σ) :
    TM2.stepAux (increment counter next) state (Function.update base counter (encodeWord n)) =
      ⟨some next, state, Function.update base counter (encodeWord (n + 1))⟩ := by
  simp [increment, TM2.stepAux, encodeWord, List.replicate_succ]

end Fuel

namespace Top

abbrev Body := MachineRegularOriginalBody.Tape
abbrev Tape := Body ⊕ (Header.Tape ⊕ Fin 4)
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineRegularOriginalBody.State × Option Bool
abbrev Data := MachineRegularMetadata.Data
abbrev BaseTable := PreprocessingRegularTables.BaseTable

private def sumDecidableEq {A B : Type} (left : DecidableEq A) (right : DecidableEq B) :
    DecidableEq (A ⊕ B)
  | .inl a, .inl b => match left a b with
      | .isTrue h => .isTrue (congrArg (Sum.inl : A → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => match right a b with
      | .isTrue h => .isTrue (congrArg (Sum.inr : B → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => .isFalse (by intro h; cases h)
  | .inr _, .inl _ => .isFalse (by intro h; cases h)

instance tapeDecidableEq : DecidableEq Tape :=
  sumDecidableEq
    (sumDecidableEq (inferInstanceAs (DecidableEq (Fin 27)))
      (sumDecidableEq (inferInstanceAs (DecidableEq MachineRegularMetadata.Extra))
        (sumDecidableEq
          (sumDecidableEq
            (sumDecidableEq (inferInstanceAs (DecidableEq MachineExpanderRow.Tape))
              (inferInstanceAs (DecidableEq MachineExpanderTable.ExtraTape)))
            (inferInstanceAs (DecidableEq MachineExpanderFamily.ExtraTape)))
          (inferInstanceAs (DecidableEq MachineCeilingPower.Tape)))))
    (sumDecidableEq
      (sumDecidableEq (inferInstanceAs (DecidableEq MachineCloudPrefix.Tape))
        (inferInstanceAs (DecidableEq Header.Extra)))
      (inferInstanceAs (DecidableEq (Fin 4))))

instance tapeBEq : BEq Tape where
  beq a b := decide (a = b)

instance tapeLawfulBEq : LawfulBEq Tape where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

instance tapeFintype : Fintype Tape := by
  change Fintype
    ((Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕
      (((MachineExpanderRow.Tape ⊕ MachineExpanderTable.ExtraTape) ⊕
        MachineExpanderFamily.ExtraTape) ⊕ MachineCeilingPower.Tape))) ⊕
      ((MachineCloudPrefix.Tape ⊕ Header.Extra) ⊕ Fin 4))
  infer_instance

def coreTape (i : Fin 27) : Tape := .inl (.inl i)
def oldFuel : Tape := .inr (.inr 0)
def ownerFuel : Tape := .inr (.inr 1)
def dummyFuel : Tape := .inr (.inr 2)
def scratch : Tape := .inr (.inr 3)

def headerTape (k : Header.Tape) : Tape :=
  if k = Header.tableTape then coreTape 0
  else if k = Header.mTape then coreTape 6
  else if k = Header.outputTape then coreTape 8
  else .inr (.inl k)

def headerView : Tape → Option Header.Tape
  | .inl (.inl i) => match i.val with
    | 0 => some Header.tableTape
    | 6 => some Header.mTape
    | 8 => some Header.outputTape
    | _ => none
  | .inl (.inr _) => none
  | .inr (.inl k) =>
      if k = Header.tableTape ∨ k = Header.mTape ∨ k = Header.outputTape then none else some k
  | .inr (.inr _) => none

theorem headerView_left (k : Header.Tape) : headerView (headerTape k) = some k := by
  by_cases ht : k = Header.tableTape
  · subst k; rfl
  by_cases hm : k = Header.mTape
  · subst k; rfl
  by_cases ho : k = Header.outputTape
  · subst k; rfl
  simp [headerTape, headerView, ht, hm, ho]

theorem headerView_right (j : Tape) (k : Header.Tape)
    (h : headerView j = some k) : headerTape k = j := by
  cases j with
  | inl j =>
    cases j with
    | inl i =>
      fin_cases i <;> simp_all [headerView] <;> subst k <;> rfl
    | inr e => cases h
  | inr j =>
    cases j with
    | inl i =>
      by_cases hi : i = Header.tableTape ∨ i = Header.mTape ∨ i = Header.outputTape
      · simp [headerView, hi] at h
      · have hik : i = k := by simpa [headerView, hi] using h
        subst k
        simp only [not_or] at hi
        simp [headerTape, hi.1, hi.2.1, hi.2.2]
    | inr i => cases h

def bodyView : Tape → Option Body
  | .inl k => some k
  | .inr _ => none

theorem bodyView_left (k : Body) : bodyView (.inl k) = some k := rfl
theorem bodyView_right (j : Tape) (k : Body)
    (h : bodyView j = some k) : Sum.inl k = j := by
  cases j with
  | inl j => cases h; rfl
  | inr j => cases h

def ownerTape : MachineRegularOwnerBody.Tape → Tape
  | .inl k => .inl k
  | .inr i => if i.val = 0 then dummyFuel else scratch

def ownerView : Tape → Option MachineRegularOwnerBody.Tape
  | .inl k => some (.inl k)
  | .inr (.inl _) => none
  | .inr (.inr i) => match i.val with
    | 2 => some (.inr 0)
    | 3 => some (.inr 1)
    | _ => none

theorem ownerView_left (k : MachineRegularOwnerBody.Tape) :
    ownerView (ownerTape k) = some k := by
  cases k with
  | inl k => rfl
  | inr i => fin_cases i <;> rfl

theorem ownerView_right (j : Tape) (k : MachineRegularOwnerBody.Tape)
    (h : ownerView j = some k) : ownerTape k = j := by
  cases j with
  | inl j => cases h; rfl
  | inr j =>
    cases j with
    | inl j => cases h
    | inr i => fin_cases i <;> simp_all [ownerView] <;> subst k <;> rfl

end Top
end IndependentSetsGames.Foundations.Complexity.MachineRegularTable

end OAI
