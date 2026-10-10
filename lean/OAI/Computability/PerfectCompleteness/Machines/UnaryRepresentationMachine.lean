import OAI.Computability.UniqueGames.Machines.MachineInitialHeaders

namespace OAI


namespace PerfectCompleteness.UnaryRepresentationMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer (loopAt exitAt)

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

inductive RawLabel
  | scan | restore
  deriving DecidableEq

protected abbrev RawLabel.enumList : List RawLabel := [.scan, .restore]

protected theorem RawLabel.enumList_getElem?_ctorIdx_eq (x : RawLabel) :
    RawLabel.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem RawLabel.enumList_nodup : RawLabel.enumList.Nodup := by decide

instance : Fintype RawLabel where
  elems := ⟨RawLabel.enumList, RawLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive EncodedLabel
  | seed | copy | restore
  deriving DecidableEq

protected abbrev EncodedLabel.enumList : List EncodedLabel := [.seed, .copy, .restore]

protected theorem EncodedLabel.enumList_getElem?_ctorIdx_eq (x : EncodedLabel) :
    EncodedLabel.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem EncodedLabel.enumList_nodup : EncodedLabel.enumList.Nodup := by decide

instance : Fintype EncodedLabel where
  elems := ⟨EncodedLabel.enumList, EncodedLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

def encodedToRawMain : RawLabel := .scan
def rawToEncodedMain : EncodedLabel := .seed

variable {K Λ A : Type} [DecidableEq K]

def encodedToRawInstruction (tape : Fin 3 → K) (labels : RawLabel → Λ)
    (done : Option Λ) : RawLabel → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .scan => MachineInitialHeaders.prefixScan (tape 0) (tape 1) (tape 2) 1
      (labels .scan) (labels .restore)
  | .restore => loopAt (tape 1) (tape 0) id false (labels .restore) done

def rawToEncodedInstruction (tape : Fin 3 → K) (labels : EncodedLabel → Λ)
    (done : Option Λ) : EncodedLabel → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .seed => .push (tape 2) (fun _ => false) (.goto fun _ => labels .copy)
  | .copy => loopAt (tape 0) (tape 1) id false (labels .copy) (some (labels .restore))
  | .restore => MachineCopy.forkLoop (tape 1) (tape 0) (tape 2) false
      (labels .restore) done

omit [DecidableEq K] in
theorem encodedToRaw_pushBound (tape : Fin 3 → K) (labels : RawLabel → Λ)
    (done : Option Λ) (label : RawLabel) :
    Runtime.statementPushBound (encodedToRawInstruction (A := A) tape labels done label) ≤ 2 := by
  cases label with
  | scan =>
      simpa only [encodedToRawInstruction, MachineInitialHeaders.prefixScan_pushBound]
        using (Nat.le_refl 2)
  | restore => cases done <;>
      simp [encodedToRawInstruction, loopAt, exitAt, Runtime.statementPushBound]

omit [DecidableEq K] in
theorem rawToEncoded_pushBound (tape : Fin 3 → K) (labels : EncodedLabel → Λ)
    (done : Option Λ) (label : EncodedLabel) :
    Runtime.statementPushBound (rawToEncodedInstruction (A := A) tape labels done label) ≤ 2 := by
  cases label <;> cases done <;>
    simp [rawToEncodedInstruction, loopAt, MachineCopy.forkLoop, exitAt,
      Runtime.statementPushBound]

theorem encodedToRawTrace (tape : Fin 3 → K) (distinct : Function.Injective tape)
    (labels : RawLabel → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = encodedToRawInstruction tape labels done label)
    (base : K → List Bool) (n : Nat) (sourceWord : base (tape 0) = encodeWord n)
    (scratchEmpty : base (tape 1) = []) (ambient : A) (register : Option Bool) :
    (advance (TM2.step program))^[2 * n + 2]
      (some ⟨some (labels encodedToRawMain), (ambient, register), base⟩) =
      some ⟨done, (ambient, none),
        Function.update base (tape 2) (List.replicate n true ++ base (tape 2))⟩ := by
  have h01 : tape 0 ≠ tape 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (distinct h)
  have h02 : tape 0 ≠ tape 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (distinct h)
  have h12 : tape 1 ≠ tape 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (distinct h)
  have trace := MachineInitialHeaders.prefixTrace (tape 0) (tape 1) (tape 2)
    h01 h02 h12 1 (labels .scan) (labels .restore) done program
    (atLabels .scan) (atLabels .restore) base n []
    (by simpa only [List.append_nil] using sourceWord) scratchEmpty ambient register
  simpa only [encodedToRawMain, Nat.one_mul] using trace

def encodedToRawInTime (tape : Fin 3 → K) (distinct : Function.Injective tape)
    (labels : RawLabel → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = encodedToRawInstruction tape labels done label)
    (base : K → List Bool) (n : Nat) (sourceWord : base (tape 0) = encodeWord n)
    (scratchEmpty : base (tape 1) = []) (ambient : A) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels encodedToRawMain), (ambient, register), base⟩
      (some ⟨done, (ambient, none),
        Function.update base (tape 2) (List.replicate n true ++ base (tape 2))⟩) (2 * n + 2) where
  steps := 2 * n + 2
  evals_in_steps := encodedToRawTrace tape distinct labels done program atLabels base n
    sourceWord scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

theorem seedStep (tape : Fin 3 → K) (labels : EncodedLabel → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atSeed : program (labels .seed) = rawToEncodedInstruction tape labels done .seed)
    (base : K → List Bool) (state : State A) :
    TM2.step program ⟨some (labels .seed), state, base⟩ =
      some ⟨some (labels .copy), state, Function.update base (tape 2) (false :: base (tape 2))⟩ := by
  change some (TM2.stepAux (program (labels .seed)) state base) = _
  rw [atSeed]
  rfl

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem rawToEncodedTrace (tape : Fin 3 → K) (distinct : Function.Injective tape)
    (labels : EncodedLabel → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = rawToEncodedInstruction tape labels done label)
    (base : K → List Bool) (n : Nat) (sourceWord : base (tape 0) = List.replicate n true)
    (scratchEmpty : base (tape 1) = []) (ambient : A) (register : Option Bool) :
    (advance (TM2.step program))^[1 + 2 * (n + 1)]
      (some ⟨some (labels rawToEncodedMain), (ambient, register), base⟩) =
      some ⟨done, (ambient, none),
        Function.update base (tape 2) (encodeWord n ++ base (tape 2))⟩ := by
  have h02 : tape 0 ≠ tape 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (distinct h)
  have h01 : tape 0 ≠ tape 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (distinct h)
  have h21 : tape 2 ≠ tape 1 := fun h => (by decide : (2 : Fin 3) ≠ 1) (distinct h)
  let seeded := Function.update base (tape 2) (false :: base (tape 2))
  have seededSource : seeded (tape 0) = List.replicate n true := by
    simp [seeded, h02, sourceWord]
  have seededScratch : seeded (tape 1) = [] := by
    simp [seeded, Ne.symm h21, scratchEmpty]
  have first : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨some (labels .copy), (ambient, register), seeded⟩ :=
    seedStep tape labels done program (atLabels .seed) base (ambient, register)
  have second := MachineCopy.copyTrace (tape 0) (tape 2) (tape 1) h02 h01 h21 false
    (labels .copy) (labels .restore) done program (atLabels .copy) (atLabels .restore)
    seeded seededScratch ambient register
  rw [seededSource, List.length_replicate] at second
  have full := joinTrace first second
  simpa only [rawToEncodedMain, seeded, Function.update_self, Function.update_idem,
    encodeWord, List.append_assoc, List.singleton_append] using full

def rawToEncodedInTime (tape : Fin 3 → K) (distinct : Function.Injective tape)
    (labels : EncodedLabel → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = rawToEncodedInstruction tape labels done label)
    (base : K → List Bool) (n : Nat) (sourceWord : base (tape 0) = List.replicate n true)
    (scratchEmpty : base (tape 1) = []) (ambient : A) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels rawToEncodedMain), (ambient, register), base⟩
      (some ⟨done, (ambient, none),
        Function.update base (tape 2) (encodeWord n ++ base (tape 2))⟩) (1 + 2 * (n + 1)) where
  steps := 1 + 2 * (n + 1)
  evals_in_steps := rawToEncodedTrace tape distinct labels done program atLabels base n
    sourceWord scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

theorem finiteState [Finite A] : Finite (State A) := inferInstance

omit [DecidableEq K] in
theorem finiteAlphabet (key : K) : Finite (Alphabet key) := by
  change Finite Bool
  infer_instance

end PerfectCompleteness.UnaryRepresentationMachine

end OAI
