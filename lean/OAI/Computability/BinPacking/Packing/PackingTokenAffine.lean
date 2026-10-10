import OAI.Computability.BinPacking.Computation.MachineHorner

namespace OAI

namespace BinPackingGap.PackingTokenAffine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction
open MachineSubstitution (pushWord stepAux_pushWord)

def transition (_ : Unit) (_ : Bool) : Unit := ()

def emit (coefficient : Nat) (_ : Unit) : Bool → List Bool
  | true => List.replicate coefficient true
  | false => []

def scanOutput (coefficient : Nat) (input : List Bool) : List Bool :=
  MachineTransducer.output transition (emit coefficient) () input

@[simp] theorem scanOutput_nil (coefficient : Nat) : scanOutput coefficient [] = [] := rfl

theorem scanOutput_cons (coefficient : Nat) (bit : Bool) (rest : List Bool) :
    scanOutput coefficient (bit :: rest) =
      emit coefficient () bit ++ scanOutput coefficient rest := rfl

theorem scanOutput_replicate_append (coefficient a : Nat) (suffix : List Bool) :
    scanOutput coefficient (List.replicate a true ++ suffix) =
      List.replicate (coefficient * a) true ++ scanOutput coefficient suffix := by
  induction a with
  | zero => simp only [List.replicate_zero, List.nil_append, Nat.mul_zero]
  | succ a ih =>
      calc
        scanOutput coefficient (List.replicate (a + 1) true ++ suffix) =
            List.replicate coefficient true ++
              (List.replicate (coefficient * a) true ++ scanOutput coefficient suffix) := by
          rw [List.replicate_succ, List.cons_append, scanOutput_cons]
          simp only [emit, ih]
        _ = List.replicate (coefficient + coefficient * a) true ++
            scanOutput coefficient suffix := by
          rw [List.replicate_add, List.append_assoc]
        _ = List.replicate (coefficient * (a + 1)) true ++
            scanOutput coefficient suffix := by
          simp only [Nat.mul_succ, Nat.add_comm]

@[simp] theorem scanOutput_replicate (coefficient a : Nat) :
    scanOutput coefficient (List.replicate a true) =
      List.replicate (coefficient * a) true := by
  simpa only [List.append_nil, scanOutput_nil] using
    scanOutput_replicate_append coefficient a []

@[simp] theorem scanOutput_encodeWord (coefficient a : Nat) :
    scanOutput coefficient (encodeWord a) = List.replicate (coefficient * a) true := by
  rw [encodeWord, scanOutput_replicate_append]
  simp only [scanOutput_cons, emit, scanOutput_nil, List.append_nil]

theorem tokens_encodeWord (a b : Nat) (suffix : List Bool) :
    List.replicate a true ++ (encodeWord b ++ suffix) =
      encodeWord (a + b) ++ suffix := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

theorem emit_length_le (coefficient : Nat) (control : Unit) (bit : Bool) :
    (emit coefficient control bit).length ≤ coefficient := by
  cases bit <;> simp [emit]

abbrev State (A : Type) := MachineTransducerCopy.State A Unit

def clean {A : Type} (ambient : A) : State A := ((ambient, ()), none)

inductive Label
  | seed
  | scan
  | restore
  | emitter (bit : Bool)
  deriving DecidableEq, Fintype

variable {K Λ A : Type} [DecidableEq K]

def instruction (coefficient offset : Nat) (slots : Fin 3 ↪ K)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State A)
  | .seed => pushWord (slots 2) (encodeWord offset).reverse
      (.goto fun _ => labels .scan)
  | .scan => MachineTransducerCopy.scanLoop (slots 0) (slots 1) ()
      (fun _ bit => labels (.emitter bit)) (labels .restore)
  | .emitter bit => MachineTransducerCopy.emitter (slots 2) transition (emit coefficient)
      (labels .scan) () bit
  | .restore => MachineTransfer.loopAt (slots 1) (slots 0) id false
      (labels .restore) exit

theorem scanTrace (coefficient offset : Nat) (slots : Fin 3 ↪ K)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State A))
    (atLabels : ∀ label,
      program (labels label) = instruction coefficient offset slots labels exit label)
    (base : K → List Bool) (scratchEmpty : base (slots 1) = []) (ambient : A) :
    (MachineComposition.advance (TM2.step program))^[3 * (base (slots 0)).length + 2]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        Function.update base (slots 2)
          ((scanOutput coefficient (base (slots 0))).reverse ++ base (slots 2))⟩ := by
  have hd (i j : Fin 3) (hne : i ≠ j) : slots i ≠ slots j := slots.injective.ne hne
  have run := MachineTransducerCopy.transduceCopyTrace (slots 0) (slots 1) (slots 2)
    (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide))
    () transition (emit coefficient) (labels .scan) (labels .restore)
    (fun _ bit => labels (.emitter bit)) exit program
    (atLabels .scan) (fun control bit => by
      cases control
      exact atLabels (.emitter bit))
    (atLabels .restore) base scratchEmpty ambient () none
  simpa only [scanOutput, clean] using run

theorem tokensTrace (coefficient offset : Nat) (slots : Fin 3 ↪ K)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State A))
    (atLabels : ∀ label,
      program (labels label) = instruction coefficient offset slots labels exit label)
    (base : K → List Bool) (a : Nat)
    (sourceWord : base (slots 0) = List.replicate a true)
    (scratchEmpty : base (slots 1) = []) (ambient : A) :
    (MachineComposition.advance (TM2.step program))^[3 * a + 2]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        Function.update base (slots 2)
          (List.replicate (coefficient * a) true ++ base (slots 2))⟩ := by
  simpa only [sourceWord, List.length_replicate, scanOutput_replicate,
    List.reverse_replicate] using
    scanTrace coefficient offset slots labels exit program atLabels base scratchEmpty ambient

theorem seedStep (coefficient offset : Nat) (slots : Fin 3 ↪ K)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State A))
    (atLabels : ∀ label,
      program (labels label) = instruction coefficient offset slots labels exit label)
    (base : K → List Bool) (state : State A) :
    TM2.step program ⟨some (labels .seed), state, base⟩ =
      some ⟨some (labels .scan), state,
        Function.update base (slots 2) (encodeWord offset ++ base (slots 2))⟩ := by
  change some (TM2.stepAux (program (labels .seed)) state base) = _
  rw [atLabels .seed]
  simp only [instruction, stepAux_pushWord, List.reverse_reverse, TM2.stepAux]

theorem seededScanTrace (coefficient offset : Nat) (slots : Fin 3 ↪ K)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State A))
    (atLabels : ∀ label,
      program (labels label) = instruction coefficient offset slots labels exit label)
    (base : K → List Bool) (scratchEmpty : base (slots 1) = []) (ambient : A) :
    (MachineComposition.advance (TM2.step program))^[3 * (base (slots 0)).length + 3]
      (some ⟨some (labels .seed), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        Function.update base (slots 2)
          ((scanOutput coefficient (base (slots 0))).reverse ++
            (encodeWord offset ++ base (slots 2)))⟩ := by
  let seeded := Function.update base (slots 2) (encodeWord offset ++ base (slots 2))
  have sourceDestination : slots 0 ≠ slots 2 := slots.injective.ne (by decide)
  have scratchDestination : slots 1 ≠ slots 2 := slots.injective.ne (by decide)
  have sourceSame : seeded (slots 0) = base (slots 0) := by
    simp [seeded, sourceDestination]
  have scratchSame : seeded (slots 1) = [] := by
    simp [seeded, scratchDestination, scratchEmpty]
  have run := scanTrace coefficient offset slots labels exit program atLabels
    seeded scratchSame ambient
  rw [sourceSame] at run
  simp only [seeded, Function.update_self, Function.update_idem] at run
  rw [show 3 * (base (slots 0)).length + 3 =
    (3 * (base (slots 0)).length + 2) + 1 by omega,
    Function.iterate_succ_apply, MachineComposition.advance_some,
    seedStep coefficient offset slots labels exit program atLabels]
  exact run

theorem seededTrace (coefficient offset : Nat) (slots : Fin 3 ↪ K)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State A))
    (atLabels : ∀ label,
      program (labels label) = instruction coefficient offset slots labels exit label)
    (base : K → List Bool) (a : Nat)
    (sourceWord : base (slots 0) = List.replicate a true)
    (scratchEmpty : base (slots 1) = []) (ambient : A) :
    (MachineComposition.advance (TM2.step program))^[3 * a + 3]
      (some ⟨some (labels .seed), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        Function.update base (slots 2)
          (encodeWord (coefficient * a + offset) ++ base (slots 2))⟩ := by
  simpa only [sourceWord, List.length_replicate, scanOutput_replicate,
    List.reverse_replicate, tokens_encodeWord] using
    seededScanTrace coefficient offset slots labels exit program atLabels base scratchEmpty ambient

theorem encodedAccumulateTrace (coefficient offset : Nat) (slots : Fin 3 ↪ K)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State A))
    (atLabels : ∀ label,
      program (labels label) = instruction coefficient offset slots labels exit label)
    (base : K → List Bool) (a b : Nat) (suffix : List Bool)
    (sourceWord : base (slots 0) = encodeWord a)
    (scratchEmpty : base (slots 1) = [])
    (destinationWord : base (slots 2) = encodeWord b ++ suffix) (ambient : A) :
    (MachineComposition.advance (TM2.step program))^[3 * (a + 1) + 2]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        Function.update base (slots 2) (encodeWord (coefficient * a + b) ++ suffix)⟩ := by
  simpa only [sourceWord, encodeWord_length, scanOutput_encodeWord,
    List.reverse_replicate, destinationWord, tokens_encodeWord] using
    scanTrace coefficient offset slots labels exit program atLabels base scratchEmpty ambient

def seededInTime (coefficient offset : Nat) (slots : Fin 3 ↪ K)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State A))
    (atLabels : ∀ label,
      program (labels label) = instruction coefficient offset slots labels exit label)
    (base : K → List Bool) (a : Nat)
    (sourceWord : base (slots 0) = List.replicate a true)
    (scratchEmpty : base (slots 1) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .seed), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        Function.update base (slots 2)
          (encodeWord (coefficient * a + offset) ++ base (slots 2))⟩)
      (3 * a + 3) where
  steps := 3 * a + 3
  evals_in_steps := seededTrace coefficient offset slots labels exit program atLabels
    base a sourceWord scratchEmpty ambient
  steps_le_m := Nat.le_refl _

def encodedAccumulateInTime (coefficient offset : Nat) (slots : Fin 3 ↪ K)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State A))
    (atLabels : ∀ label,
      program (labels label) = instruction coefficient offset slots labels exit label)
    (base : K → List Bool) (a b : Nat) (suffix : List Bool)
    (sourceWord : base (slots 0) = encodeWord a)
    (scratchEmpty : base (slots 1) = [])
    (destinationWord : base (slots 2) = encodeWord b ++ suffix) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        Function.update base (slots 2) (encodeWord (coefficient * a + b) ++ suffix)⟩)
      (3 * (a + 1) + 2) where
  steps := 3 * (a + 1) + 2
  evals_in_steps := encodedAccumulateTrace coefficient offset slots labels exit program atLabels
    base a b suffix sourceWord scratchEmpty destinationWord ambient
  steps_le_m := Nat.le_refl _

end BinPackingGap.PackingTokenAffine

end OAI
