import OAI.Computability.BinPacking.Arithmetic.BinaryPowerMachine
import OAI.Computability.BinPacking.Arithmetic.NatExpression
import OAI.Computability.BinPacking.Arithmetic.PackingRegisterFrame
import OAI.Computability.BinPacking.Computation.MachineCanonicalOutput

namespace OAI

namespace BinPackingGap.BinaryAddPreserving

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer
open BinaryAddMachine (State clean)

variable {K Λ A : Type} [DecidableEq K]

inductive Label
  | leftOut | leftBack | rightOut | rightBack | add | transfer
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.leftOut, .leftBack, .rightOut, .rightBack, .add,
  .transfer]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def instruction (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A)
  | .leftOut => loopAt (slots 0) (slots 6) id false
      (labels .leftOut) (some (labels .leftBack))
  | .leftBack => MachineCopy.forkLoop (slots 6) (slots 0) (slots 2) false
      (labels .leftBack) (some (labels .rightOut))
  | .rightOut => loopAt (slots 1) (slots 6) id false
      (labels .rightOut) (some (labels .rightBack))
  | .rightBack => MachineCopy.forkLoop (slots 6) (slots 1) (slots 3) false
      (labels .rightBack) (some (labels .add))
  | .add => BinaryAddMachine.addLoop (slots 2) (slots 3) (slots 4)
      (labels .add) (some (labels .transfer))
  | .transfer => loopAt (slots 4) (slots 5) id false (labels .transfer) exit

def resultTapes (slots : Fin 7 ↪ K) (base : K → List Bool) (a b : Nat) : K → List Bool :=
  Function.update base (slots 5) (a + b).bits

@[simp] theorem resultTapes_output (slots : Fin 7 ↪ K) (base : K → List Bool) (a b : Nat) :
    resultTapes slots base a b (slots 5) = (a + b).bits := by simp [resultTapes]

theorem resultTapes_other (slots : Fin 7 ↪ K) (base : K → List Bool) (a b : Nat)
    (k : K) (outside : k ≠ slots 5) : resultTapes slots base a b k = base k := by
  simp [resultTapes, outside]

def steps (a b : Nat) : Nat :=
  2 * (a.size + 1) + 2 * (b.size + 1) + (max a.size b.size + 1) + ((a + b).size + 1)

theorem steps_le (a b : Nat) : steps a b ≤ 4 * (a.size + b.size) + 7 := by
  have sumLength := BinaryArithmetic.size_add_le a b
  unfold steps
  omega

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem addTrace (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction slots labels exit label)
    (base : K → List Bool) (a b : Nat)
    (leftWord : base (slots 0) = a.bits) (rightWord : base (slots 1) = b.bits)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (sumEmpty : base (slots 4) = []) (outputEmpty : base (slots 5) = [])
    (scratchEmpty : base (slots 6) = []) (ambient : A) :
    (MachineComposition.advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .leftOut), clean ambient, base⟩) =
      some ⟨exit, clean ambient, resultTapes slots base a b⟩ := by
  have hd (i j : Fin 7) (hne : i ≠ j) : slots i ≠ slots j := slots.injective.ne hne
  let afterLeft := Function.update base (slots 2) a.bits
  let afterBoth := Function.update afterLeft (slots 3) b.bits
  let afterAdd := Function.update base (slots 4) (a + b).bits.reverse
  have leftRun : (MachineComposition.advance (TM2.step program))^[2 * (a.size + 1)]
      (some ⟨some (labels .leftOut), clean ambient, base⟩) =
      some ⟨some (labels .rightOut), clean ambient, afterLeft⟩ := by
    have run := MachineCopy.copyTrace (slots 0) (slots 2) (slots 6)
      (hd 0 2 (by decide)) (hd 0 6 (by decide)) (hd 2 6 (by decide)) false
      (labels .leftOut) (labels .leftBack) (some (labels .rightOut)) program
      (atLabels .leftOut) (atLabels .leftBack) base scratchEmpty
      ((ambient, false), none) none
    simpa only [leftWord, leftEmpty, List.append_nil, Nat.size_eq_bits_len,
      clean, BinaryAddMachine.state, afterLeft] using run
  have rightStill : afterLeft (slots 1) = b.bits := by
    simp [afterLeft, hd 1 2 (by decide), rightWord]
  have rightCopyEmpty : afterLeft (slots 3) = [] := by
    simp [afterLeft, hd 3 2 (by decide), rightEmpty]
  have scratchStill : afterLeft (slots 6) = [] := by
    simp [afterLeft, hd 6 2 (by decide), scratchEmpty]
  have rightRun : (MachineComposition.advance (TM2.step program))^[2 * (b.size + 1)]
      (some ⟨some (labels .rightOut), clean ambient, afterLeft⟩) =
      some ⟨some (labels .add), clean ambient, afterBoth⟩ := by
    have run := MachineCopy.copyTrace (slots 1) (slots 3) (slots 6)
      (hd 1 3 (by decide)) (hd 1 6 (by decide)) (hd 3 6 (by decide)) false
      (labels .rightOut) (labels .rightBack) (some (labels .add)) program
      (atLabels .rightOut) (atLabels .rightBack) afterLeft scratchStill
      ((ambient, false), none) none
    simpa only [rightStill, rightCopyEmpty, List.append_nil, Nat.size_eq_bits_len,
      clean, BinaryAddMachine.state, afterBoth] using run
  have leftCopied : afterBoth (slots 2) = a.bits := by
    simp [afterBoth, afterLeft, hd 2 3 (by decide)]
  have rightCopied : afterBoth (slots 3) = b.bits := by simp [afterBoth]
  have sumStillEmpty : afterBoth (slots 4) = [] := by
    simp [afterBoth, afterLeft, hd 4 3 (by decide), hd 4 2 (by decide), sumEmpty]
  have addStart : BinaryAddMachine.tapes (slots 2) (slots 3) (slots 4)
      afterBoth a.bits b.bits [] = afterBoth := by
    have self : BinaryAddMachine.tapes (slots 2) (slots 3) (slots 4) afterBoth
        (afterBoth (slots 2)) (afterBoth (slots 3)) (afterBoth (slots 4)) = afterBoth := by
      simp [BinaryAddMachine.tapes]
    simpa only [leftCopied, rightCopied, sumStillEmpty] using self
  have addFinish : BinaryAddMachine.tapes (slots 2) (slots 3) (slots 4)
      afterBoth [] [] (a + b).bits.reverse = afterAdd := by
    funext k
    by_cases hl : k = slots 2
    · subst k
      simp [BinaryAddMachine.tapes, afterAdd, hd 2 3 (by decide),
        hd 2 4 (by decide), leftEmpty]
    · by_cases hr : k = slots 3
      · subst k
        simp [BinaryAddMachine.tapes, afterAdd, hd 3 4 (by decide), rightEmpty]
      · by_cases hs : k = slots 4
        · subst k
          simp [BinaryAddMachine.tapes, afterAdd]
        · simp [BinaryAddMachine.tapes, afterAdd, afterBoth, afterLeft, hl, hr, hs]
  have sumRun : (MachineComposition.advance (TM2.step program))^[max a.size b.size + 1]
      (some ⟨some (labels .add), clean ambient, afterBoth⟩) =
      some ⟨some (labels .transfer), clean ambient, afterAdd⟩ := by
    have run := BinaryAddMachine.addTrace (slots 2) (slots 3) (slots 4)
      (hd 2 3 (by decide)) (hd 2 4 (by decide)) (hd 3 4 (by decide))
      (labels .add) (some (labels .transfer)) program (atLabels .add) afterBoth ambient
      a.bits b.bits [] false none none
    simpa only [BinaryArithmetic.addCarry_bits, List.append_nil, Nat.size_eq_bits_len,
      addStart, addFinish, clean] using run
  have sumWord : afterAdd (slots 4) = (a + b).bits.reverse := by simp [afterAdd]
  have outputStillEmpty : afterAdd (slots 5) = [] := by
    simp [afterAdd, hd 5 4 (by decide), outputEmpty]
  have transferred : tapesAt (slots 4) (slots 5) afterAdd [] (a + b).bits =
      resultTapes slots base a b := by
    funext k
    by_cases ho : k = slots 5
    · subst k
      simp [tapesAt, resultTapes]
    · by_cases hs : k = slots 4
      · subst k
        simp [tapesAt, resultTapes, hd 4 5 (by decide), sumEmpty]
      · simp [tapesAt, resultTapes, afterAdd, ho, hs]
  have transferRun : (MachineComposition.advance (TM2.step program))^[(a + b).size + 1]
      (some ⟨some (labels .transfer), clean ambient, afterAdd⟩) =
      some ⟨exit, clean ambient, resultTapes slots base a b⟩ := by
    have run := transferAt_fromTapes (Γ := fun _ : K => Bool) (slots 4) (slots 5)
      (hd 4 5 (by decide)) id false (labels .transfer) exit program (atLabels .transfer)
      afterAdd ((ambient, false), none) none
    have hnext : nextAt (Γ := fun _ : K => Bool) (slots 5) program =
        MachineComposition.advance (TM2.step program) := rfl
    simpa only [hnext,
      sumWord, outputStillEmpty, List.reverse_reverse, List.length_reverse,
      List.map_id, List.append_nil, Nat.size_eq_bits_len, transferred,
      clean, BinaryAddMachine.state] using run
  exact joinTrace (joinTrace (joinTrace leftRun rightRun) sumRun) transferRun

def addInTime (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction slots labels exit label)
    (base : K → List Bool) (a b : Nat)
    (leftWord : base (slots 0) = a.bits) (rightWord : base (slots 1) = b.bits)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (sumEmpty : base (slots 4) = []) (outputEmpty : base (slots 5) = [])
    (scratchEmpty : base (slots 6) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftOut), clean ambient, base⟩
      (some ⟨exit, clean ambient, resultTapes slots base a b⟩)
      (steps a b) where
  steps := steps a b
  evals_in_steps := addTrace slots labels exit program atLabels base a b leftWord rightWord
    leftEmpty rightEmpty sumEmpty outputEmpty scratchEmpty ambient
  steps_le_m := Nat.le_refl _

def addInLinearTime (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction slots labels exit label)
    (base : K → List Bool) (a b : Nat)
    (leftWord : base (slots 0) = a.bits) (rightWord : base (slots 1) = b.bits)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (sumEmpty : base (slots 4) = []) (outputEmpty : base (slots 5) = [])
    (scratchEmpty : base (slots 6) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftOut), clean ambient, base⟩
      (some ⟨exit, clean ambient, resultTapes slots base a b⟩)
      (4 * (a.size + b.size) + 7) where
  steps := steps a b
  evals_in_steps := addTrace slots labels exit program atLabels base a b leftWord rightWord
    leftEmpty rightEmpty sumEmpty outputEmpty scratchEmpty ambient
  steps_le_m := steps_le a b

def machine : FinTM2 where
  K := Fin 7
  k₀ := 0
  k₁ := 5
  Γ _ := Bool
  Λ := Label
  main := .leftOut
  σ := State Unit
  initialState := clean ()
  m := instruction (Function.Embedding.refl (Fin 7)) id none

theorem machine_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet machine := by
  intro tape
  change Finite Bool
  infer_instance

end BinPackingGap.BinaryAddPreserving

namespace BinPackingGap.BinaryMonusMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinaryArithmetic BinaryAddMachine

variable {K Λ A : Type} [DecidableEq K]

def subtractLoop (left right output : K) (again : Λ) (exits : Bool → Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop left (fun s head => ((s.1.1, head), s.2))
    (.pop right (fun s head => (s.1, head))
      (.branch (fun s => s.1.2.isNone && s.2.isNone)
        (.branch (fun s => s.1.1.2) (finish (exits true)) (finish (exits false)))
        (.push output (fun s => diffBit (s.1.2.getD false) (s.2.getD false) s.1.1.2)
          (.load (fun s => state s.1.1.1
            (borrowBit (s.1.2.getD false) (s.2.getD false) s.1.1.2) none none)
            (.goto fun _ => again)))))

section Subtract

variable (left right output : K)
variable (hLR : left ≠ right) (hLO : left ≠ output) (hRO : right ≠ output)
variable (again : Λ) (exits : Bool → Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atSub : program again = subtractLoop left right output again exits)
variable (base : K → List Bool) (ambient : A)

include hLR hLO hRO atSub

theorem step_done (out : List Bool) (borrow : Bool) (lreg rreg : Option Bool) :
    TM2.step program
      ⟨some again, state ambient borrow lreg rreg, tapes left right output base [] [] out⟩ =
      some ⟨exits borrow, clean ambient, tapes left right output base [] [] out⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atSub]
  cases borrow <;> cases hx : exits true <;> cases hy : exits false <;>
    simp [subtractLoop, finish, exitAt, clean, state, TM2.stepAux,
      hLR, hLO, hRO, tapes_left, tapes_right, update_left, update_right, hx, hy]

theorem step_more (xs ys out : List Bool) (borrow : Bool) (lreg rreg : Option Bool)
    (more : xs ≠ [] ∨ ys ≠ []) :
    TM2.step program
      ⟨some again, state ambient borrow lreg rreg, tapes left right output base xs ys out⟩ =
      some ⟨some again, state ambient
        (borrowBit (xs.headD false) (ys.headD false) borrow) none none,
        tapes left right output base xs.tail ys.tail
          (diffBit (xs.headD false) (ys.headD false) borrow :: out)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atSub]
  cases xs with
  | nil =>
      cases ys with
      | nil => simp at more
      | cons y ys =>
          simp [subtractLoop, state, TM2.stepAux, hLR, hLO, hRO,
            tapes_left, tapes_right, update_left, update_right, update_output]
  | cons x xs =>
      cases ys <;>
        simp [subtractLoop, state, TM2.stepAux, hLR, hLO, hRO,
          tapes_left, tapes_right, update_left, update_right, update_output]

theorem subtractTrace (xs ys out : List Bool) (borrow : Bool) (lreg rreg : Option Bool) :
    (advance (TM2.step program))^[max xs.length ys.length + 1]
      (some ⟨some again, state ambient borrow lreg rreg,
        tapes left right output base xs ys out⟩) =
      some ⟨exits (rawSubtract xs ys borrow).2, clean ambient,
        tapes left right output base [] [] ((rawSubtract xs ys borrow).1.reverse ++ out)⟩ := by
  induction xs generalizing ys out borrow lreg rreg with
  | nil =>
      induction ys generalizing out borrow lreg rreg with
      | nil =>
          simpa [rawSubtract, List.length_nil, advance_some] using
            step_done left right output hLR hLO hRO again exits program atSub base ambient
              out borrow lreg rreg
      | cons y ys ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply]
          simp only [advance_some]
          rw [step_more left right output hLR hLO hRO again exits program atSub base ambient
            [] (y :: ys) out borrow lreg rreg (Or.inr (List.cons_ne_nil _ _))]
          simpa [rawSubtract, List.reverse_cons, List.append_assoc] using
            ih (diffBit false y borrow :: out) (borrowBit false y borrow) none none
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp only [List.length_cons, List.length_nil, Nat.max_zero]
          rw [Function.iterate_succ_apply]
          simp only [advance_some]
          rw [step_more left right output hLR hLO hRO again exits program atSub base ambient
            (x :: xs) [] out borrow lreg rreg (Or.inl (List.cons_ne_nil _ _))]
          simpa [rawSubtract, List.reverse_cons, List.append_assoc] using
            ih [] (diffBit x false borrow :: out) (borrowBit x false borrow) none none
      | cons y ys =>
          rw [show max (x :: xs).length (y :: ys).length + 1 =
            (max xs.length ys.length + 1) + 1 by simp]
          rw [Function.iterate_succ_apply]
          simp only [advance_some]
          rw [step_more left right output hLR hLO hRO again exits program atSub base ambient
            (x :: xs) (y :: ys) out borrow lreg rreg (Or.inl (List.cons_ne_nil _ _))]
          simpa [rawSubtract, List.reverse_cons, List.append_assoc] using
            ih ys (diffBit x y borrow :: out) (borrowBit x y borrow) none none

def subtractInTime (xs ys out : List Bool) (borrow : Bool) (lreg rreg : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, state ambient borrow lreg rreg, tapes left right output base xs ys out⟩
      (some ⟨exits (rawSubtract xs ys borrow).2, clean ambient,
        tapes left right output base [] [] ((rawSubtract xs ys borrow).1.reverse ++ out)⟩)
      (max xs.length ys.length + 1) where
  steps := max xs.length ys.length + 1
  evals_in_steps := subtractTrace left right output hLR hLO hRO again exits program atSub
    base ambient xs ys out borrow lreg rreg
  steps_le_m := Nat.le_refl _

end Subtract

variable {σ : Type}

def trimSteps : List Bool → Nat
  | false :: xs => trimSteps xs + 1
  | _ => 1

theorem trimSteps_le (xs : List Bool) : trimSteps xs ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [trimSteps]
  | cons bit xs ih =>
      cases bit <;> simp [trimSteps]
      omega

def trimLoop (source : K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun s bit => (s.1, bit))
    (.branch (fun s => s.2.isNone)
      (.load (fun s => (s.1, none)) (BinPackingGames.Reduction.MachineTransfer.exitAt source exit))
      (.branch (fun s => s.2.getD false)
        (.push source (fun _ => true)
          (.load (fun s => (s.1, none))
            (BinPackingGames.Reduction.MachineTransfer.exitAt source exit)))
        (.goto fun _ => again)))

theorem trimTrace (source : K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atTrim : program again = trimLoop source again exit)
    (base : K → List Bool) (word : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[trimSteps word]
      (some ⟨some again, (ambient, register), Function.update base source word⟩) =
      some ⟨exit, (ambient, none), Function.update base source (trimHigh word)⟩ := by
  induction word generalizing register with
  | nil =>
      change some (TM2.stepAux (program again) _ _) = _
      rw [atTrim]
      cases exit <;>
        simp [trimLoop, trimHigh, TM2.stepAux, BinPackingGames.Reduction.MachineTransfer.exitAt]
  | cons bit word ih =>
      cases bit with
      | false =>
          rw [trimSteps, Function.iterate_succ_apply]
          change (advance (TM2.step program))^[trimSteps word]
            (some (TM2.stepAux (program again) _ _)) = _
          rw [atTrim]
          simpa [trimLoop, trimHigh, TM2.stepAux] using ih (some false)
      | true =>
          change some (TM2.stepAux (program again) _ _) = _
          rw [atTrim]
          cases exit <;>
            simp [trimLoop, trimHigh, TM2.stepAux, BinPackingGames.Reduction.MachineTransfer.exitAt]

def trimInTime (source : K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atTrim : program again = trimLoop source again exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), Function.update base source (trimHigh (base source))⟩)
      ((base source).length + 1) where
  steps := trimSteps (base source)
  evals_in_steps := by
    change (advance (TM2.step program))^[trimSteps (base source)]
      (some ⟨some again, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Function.update base source (trimHigh (base source))⟩
    simpa only [Function.update_eq_self] using
      trimTrace source again exit program atTrim base (base source) ambient register
  steps_le_m := trimSteps_le _

end BinPackingGap.BinaryMonusMachine

namespace BinPackingGap.BinaryMonusPreserving

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer
open BinaryAddMachine (State clean)
open BinaryArithmetic

variable {K Λ A : Type} [DecidableEq K]

inductive Label
  | leftOut | leftBack | rightOut | rightBack | subtract | trim | transfer | drain
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.leftOut, .leftBack, .rightOut, .rightBack,
  .subtract, .trim, .transfer, .drain]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def instruction (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A)
  | .leftOut => loopAt (slots 0) (slots 6) id false
      (labels .leftOut) (some (labels .leftBack))
  | .leftBack => MachineCopy.forkLoop (slots 6) (slots 0) (slots 2) false
      (labels .leftBack) (some (labels .rightOut))
  | .rightOut => loopAt (slots 1) (slots 6) id false
      (labels .rightOut) (some (labels .rightBack))
  | .rightBack => MachineCopy.forkLoop (slots 6) (slots 1) (slots 3) false
      (labels .rightBack) (some (labels .subtract))
  | .subtract => BinaryMonusMachine.subtractLoop (slots 2) (slots 3) (slots 4)
      (labels .subtract) (fun borrow => some (labels (if borrow then .drain else .trim)))
  | .trim => BinaryMonusMachine.trimLoop (slots 4) (labels .trim) (some (labels .transfer))
  | .transfer => loopAt (slots 4) (slots 5) id false (labels .transfer) exit
  | .drain => MachineDrain.drain (slots 4) (labels .drain) exit

def resultTapes (slots : Fin 7 ↪ K) (base : K → List Bool) (a b : Nat) : K → List Bool :=
  Function.update base (slots 5) (a - b).bits

theorem resultTapes_other (slots : Fin 7 ↪ K) (base : K → List Bool) (a b : Nat)
    (k : K) (hk : k ≠ slots 5) : resultTapes slots base a b k = base k := by
  simp [resultTapes, hk]

def budget (a b : Nat) : Nat :=
  2 * (a.size + 1) + 2 * (b.size + 1) + 3 * (max a.size b.size + 1)

theorem budget_le (a b : Nat) : budget a b ≤ 5 * (a.size + b.size) + 7 := by
  unfold budget
  omega

private def appendRuns {X : Type} (step : X → Option X) {a b c : X} {m n : Nat}
    (first : StateTransition.EvalsToInTime step a (some b) m)
    (second : StateTransition.EvalsToInTime step b (some c) n) :
    StateTransition.EvalsToInTime step a (some c) (m + n) where
  steps := first.steps + second.steps
  evals_in_steps := by
    have firstTrace := first.evals_in_steps
    have secondTrace := second.evals_in_steps
    change (MachineComposition.advance step)^[first.steps] (some a) = some b at firstTrace
    change (MachineComposition.advance step)^[second.steps] (some b) = some c at secondTrace
    change (MachineComposition.advance step)^[first.steps + second.steps] (some a) = some c
    rw [Nat.add_comm, Function.iterate_add_apply, firstTrace, secondTrace]
  steps_le_m := Nat.add_le_add first.steps_le_m second.steps_le_m

private def enlarge {X : Type} {step : X → Option X} {a : X} {b : Option X} {m n : Nat}
    (run : StateTransition.EvalsToInTime step a b m) (h : m ≤ n) :
    StateTransition.EvalsToInTime step a b n where
  steps := run.steps
  evals_in_steps := run.evals_in_steps
  steps_le_m := run.steps_le_m.trans h

def monusInTime (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, p (labels label) = instruction slots labels exit label)
    (base : K → List Bool) (a b : Nat)
    (ha : base (slots 0) = a.bits) (hb : base (slots 1) = b.bits)
    (workspace : ∀ i : Fin 7, 2 ≤ i.val → base (slots i) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .leftOut), clean ambient, base⟩
      (some ⟨exit, clean ambient, resultTapes slots base a b⟩) (budget a b) := by
  have hd (i j : Fin 7) (h : i ≠ j) : slots i ≠ slots j := slots.injective.ne h
  have h2 := workspace 2 (by decide)
  have h3 := workspace 3 (by decide)
  have h4 := workspace 4 (by decide)
  have h5 := workspace 5 (by decide)
  have h6 := workspace 6 (by decide)
  let bl := Function.update base (slots 2) a.bits
  let bb := Function.update bl (slots 3) b.bits
  let raw := rawSubtract a.bits b.bits false
  let bs := Function.update base (slots 4) raw.1.reverse
  have rawLength : raw.1.length = max a.size b.size := by
    simpa [raw, Nat.size_eq_bits_len] using rawSubtract_length a.bits b.bits false
  have rawResult : (a - b).bits = if raw.2 then [] else trim raw.1 := by
    rw [← monus_bits, monus, subBorrow_eq_rawSubtract]
    change trim ((if raw.2 then none else some raw.1).getD []) = _
    cases raw.2 <;> simp [trim]
  have leftRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .leftOut), clean ambient, base⟩
      (some ⟨some (labels .rightOut), clean ambient, bl⟩) (2 * (a.size + 1)) := by
    have run := MachineCopy.copyInTime (slots 0) (slots 2) (slots 6)
      (hd 0 2 (by decide)) (hd 0 6 (by decide)) (hd 2 6 (by decide)) false
      (labels .leftOut) (labels .leftBack) (some (labels .rightOut)) p
      (atLabels .leftOut) (atLabels .leftBack) base h6 ((ambient, false), none) none
    simpa [clean, BinaryAddMachine.state, ha, h2, bl, Nat.size_eq_bits_len] using run
  have rightRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .rightOut), clean ambient, bl⟩
      (some ⟨some (labels .subtract), clean ambient, bb⟩) (2 * (b.size + 1)) := by
    have scratch : bl (slots 6) = [] := by simp [bl, hd 6 2 (by decide), h6]
    have run := MachineCopy.copyInTime (slots 1) (slots 3) (slots 6)
      (hd 1 3 (by decide)) (hd 1 6 (by decide)) (hd 3 6 (by decide)) false
      (labels .rightOut) (labels .rightBack) (some (labels .subtract)) p
      (atLabels .rightOut) (atLabels .rightBack) bl scratch ((ambient, false), none) none
    simpa [clean, BinaryAddMachine.state, bl, bb, hd 1 2 (by decide),
      hd 3 2 (by decide), hb, h3, Nat.size_eq_bits_len] using run
  have subStart : BinaryAddMachine.tapes (slots 2) (slots 3) (slots 4)
      bb a.bits b.bits [] = bb := by
    have hleft : bb (slots 2) = a.bits := by simp [bb, bl, hd 2 3 (by decide)]
    have hright : bb (slots 3) = b.bits := by simp [bb]
    have hout : bb (slots 4) = [] := by
      simp [bb, bl, hd 4 3 (by decide), hd 4 2 (by decide), h4]
    have self : BinaryAddMachine.tapes (slots 2) (slots 3) (slots 4) bb
        (bb (slots 2)) (bb (slots 3)) (bb (slots 4)) = bb := by simp [BinaryAddMachine.tapes]
    simpa only [hleft, hright, hout] using self
  have subFinish : BinaryAddMachine.tapes (slots 2) (slots 3) (slots 4)
      bb [] [] raw.1.reverse = bs := by
    funext k
    by_cases hl : k = slots 2
    · subst k
      simp [BinaryAddMachine.tapes, bs, hd 2 3 (by decide), hd 2 4 (by decide), h2]
    · by_cases hr : k = slots 3
      · subst k
        simp [BinaryAddMachine.tapes, bs, hd 3 4 (by decide), h3]
      · by_cases hs : k = slots 4
        · subst k; simp [BinaryAddMachine.tapes, bs]
        · simp [BinaryAddMachine.tapes, bs, bb, bl, hl, hr, hs]
  have subRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .subtract), clean ambient, bb⟩
      (some ⟨some (labels (if raw.2 then .drain else .trim)), clean ambient, bs⟩)
      (max a.size b.size + 1) := by
    have run := BinaryMonusMachine.subtractInTime (slots 2) (slots 3) (slots 4)
      (hd 2 3 (by decide)) (hd 2 4 (by decide)) (hd 3 4 (by decide))
      (labels .subtract) (fun borrow => some (labels (if borrow then .drain else .trim)))
      p (atLabels .subtract) bb ambient a.bits b.bits [] false none none
    simpa only [subStart, List.append_nil, subFinish, Nat.size_eq_bits_len,
      clean, raw] using run
  have prefixRun := appendRuns _ (appendRuns _ leftRun rightRun) subRun
  cases hborrow : raw.2 with
  | true =>
      have hzero : (a - b).bits = [] := by simpa [hborrow] using rawResult
      have hfinish : Function.update bs (slots 4) [] = resultTapes slots base a b := by
        funext k
        by_cases hs : k = slots 4
        · subst k
          simp [bs, resultTapes, hzero, hd 4 5 (by decide), h4]
        · by_cases ho : k = slots 5
          · subst k
            simp [bs, resultTapes, hzero, hd 5 4 (by decide), h5]
          · simp [bs, resultTapes, hs, ho]
      have run := MachineDrain.drainInTime (slots 4) (labels .drain) exit p
        (atLabels .drain) bs ((ambient, false), none) none
      have drainRun : StateTransition.EvalsToInTime (TM2.step p)
          ⟨some (labels .drain), clean ambient, bs⟩
          (some ⟨exit, clean ambient, resultTapes slots base a b⟩)
          (max a.size b.size + 1) := by
        simpa only [clean, BinaryAddMachine.state, hfinish, bs, Function.update_self,
          List.length_reverse, rawLength] using run
      have before : StateTransition.EvalsToInTime (TM2.step p)
          ⟨some (labels .leftOut), clean ambient, base⟩
          (some ⟨some (labels .drain), clean ambient, bs⟩)
          (2 * (a.size + 1) + 2 * (b.size + 1) + (max a.size b.size + 1)) := by
        simpa only [hborrow, ite_true] using prefixRun
      exact enlarge (appendRuns _ before drainRun) (by unfold budget; omega)
  | false =>
      have hcanonical : trim raw.1 = (a - b).bits := by simpa [hborrow] using rawResult.symm
      let bt := Function.update base (slots 4) (a - b).bits.reverse
      have htrim : Function.update bs (slots 4) (trimHigh (bs (slots 4))) = bt := by
        simp [bs, bt, trimHigh_reverse, hcanonical]
      have trimRun : StateTransition.EvalsToInTime (TM2.step p)
          ⟨some (labels .trim), clean ambient, bs⟩
          (some ⟨some (labels .transfer), clean ambient, bt⟩)
          (max a.size b.size + 1) := by
        have run := BinaryMonusMachine.trimInTime (slots 4) (labels .trim)
          (some (labels .transfer)) p (atLabels .trim) bs ((ambient, false), none) none
        rw [htrim] at run
        simpa only [clean, BinaryAddMachine.state, bs, Function.update_self,
          List.length_reverse, rawLength] using run
      have outputEmpty : bt (slots 5) = [] := by simp [bt, hd 5 4 (by decide), h5]
      have htransfer : tapesAt (slots 4) (slots 5) bt [] (a - b).bits =
          resultTapes slots base a b := by
        funext k
        by_cases ho : k = slots 5
        · subst k; simp [tapesAt, resultTapes]
        · by_cases hs : k = slots 4
          · subst k; simp [tapesAt, resultTapes, hd 4 5 (by decide), h4]
          · simp [tapesAt, resultTapes, bt, ho, hs]
      have transferRun : StateTransition.EvalsToInTime (TM2.step p)
          ⟨some (labels .transfer), clean ambient, bt⟩
          (some ⟨exit, clean ambient, resultTapes slots base a b⟩)
          ((a - b).size + 1) := by
        have atTransfer : p (labels .transfer) =
            loopAt (Γ := fun _ : K => Bool) (slots 4) (slots 5) (id : Bool → Bool) false
              (labels .transfer) exit := by
          simpa only [instruction] using atLabels .transfer
        have run := transferAtInTime (Γ := fun _ : K => Bool) (slots 4) (slots 5)
          (hd 4 5 (by decide)) (id : Bool → Bool) false
          (labels .transfer) exit p atTransfer bt ((ambient, false), none) none
        have word : bt (slots 4) = (a - b).bits.reverse := by simp [bt]
        simpa only [clean, BinaryAddMachine.state, word,
          List.length_reverse, List.reverse_reverse, List.map_id, outputEmpty,
          List.append_nil, Nat.size_eq_bits_len, htransfer] using run
      have before : StateTransition.EvalsToInTime (TM2.step p)
          ⟨some (labels .leftOut), clean ambient, base⟩
          (some ⟨some (labels .trim), clean ambient, bs⟩)
          (2 * (a.size + 1) + 2 * (b.size + 1) + (max a.size b.size + 1)) := by
        simpa only [hborrow, Bool.false_eq_true, ite_false] using prefixRun
      have hsize := size_monus_le a b
      exact enlarge (appendRuns _ (appendRuns _ before trimRun) transferRun)
        (by unfold budget; omega)

def monusInLinearTime (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, p (labels label) = instruction slots labels exit label)
    (base : K → List Bool) (a b : Nat)
    (ha : base (slots 0) = a.bits) (hb : base (slots 1) = b.bits)
    (workspace : ∀ i : Fin 7, 2 ≤ i.val → base (slots i) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .leftOut), clean ambient, base⟩
      (some ⟨exit, clean ambient, resultTapes slots base a b⟩)
      (5 * (a.size + b.size) + 7) :=
  enlarge (monusInTime slots labels exit p atLabels base a b ha hb workspace ambient)
    (budget_le a b)

def machine : FinTM2 where
  K := Fin 7
  k₀ := 0
  k₁ := 5
  Γ _ := Bool
  Λ := Label
  main := .leftOut
  σ := State Unit
  initialState := clean ()
  m := instruction (Function.Embedding.refl (Fin 7)) id none

theorem machine_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet machine := by
  intro k
  change Finite Bool
  infer_instance

end BinPackingGap.BinaryMonusPreserving

namespace BinPackingGap.BinaryRegisterProgram

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

inductive Command (Reg : Type)
  | add (op : Operands Reg)
  | mul (op : Operands Reg)
  | monus (op : Operands Reg)
  | constant (dst : Reg) (value : Nat)
  | clear (dst : Reg)
  | copy (dst src : Reg) (different : dst ≠ src)

variable {Reg K Λ A : Type}

def destination : Command Reg → Reg
  | .add op | .mul op | .monus op => op.destination
  | .constant dst _ | .clear dst | .copy dst _ _ => dst

def value (command : Command Reg) (values : Reg → Nat) : Nat :=
  match command with
  | .add op => values op.left + values op.right
  | .mul op => values op.left * values op.right
  | .monus op => values op.left - values op.right
  | .constant _ n => n
  | .clear _ => 0
  | .copy _ src _ => values src

def result [DecidableEq Reg] (command : Command Reg) (values : Reg → Nat) : Reg → Nat :=
  Function.update values (destination command) (value command values)

def commandReady (command : Command Reg) (values : Reg → Nat) : Prop :=
  match command with
  | .clear _ => True
  | _ => values (destination command) = 0

def Ready [DecidableEq Reg] : List (Command Reg) → (Reg → Nat) → Prop
  | [], _ => True
  | command :: commands, values =>
      commandReady command values ∧ Ready commands (result command values)

def resultOf [DecidableEq Reg] : List (Command Reg) → (Reg → Nat) → Reg → Nat :=
  MachineFiniteSequence.resultOf result

@[simp] theorem result_destination [DecidableEq Reg] (command : Command Reg)
    (values : Reg → Nat) : result command values (destination command) = value command values := by
  simp [result]

theorem result_other [DecidableEq Reg] (command : Command Reg) (values : Reg → Nat)
    (r : Reg) (h : r ≠ destination command) : result command values r = values r := by
  simp [result, h]

@[simp] theorem resultOf_nil [DecidableEq Reg] (values : Reg → Nat) : resultOf [] values = values := rfl

@[simp] theorem resultOf_cons [DecidableEq Reg] (command : Command Reg)
    (commands : List (Command Reg)) (values : Reg → Nat) :
    resultOf (command :: commands) values = resultOf commands (result command values) := rfl

theorem resultOf_append [DecidableEq Reg] (first second : List (Command Reg))
    (values : Reg → Nat) :
    resultOf (first ++ second) values = resultOf second (resultOf first values) := by
  induction first generalizing values with
  | nil => rfl
  | cons command commands ih => exact ih (result command values)

theorem Ready_append [DecidableEq Reg] (first second : List (Command Reg))
    (values : Reg → Nat) :
    Ready (first ++ second) values ↔ Ready first values ∧ Ready second (resultOf first values) := by
  induction first generalizing values with
  | nil => simp [Ready]
  | cons command commands ih =>
      simp only [List.cons_append, Ready, resultOf_cons, ih, and_assoc]

def cost (command : Command Reg) (values : Reg → Nat) : Nat :=
  match command with
  | .add op => 4 * ((values op.left).size + (values op.right).size) + 7
  | .mul op =>
      let width := (values op.left).size + (values op.right).size
      4 * width ^ 2 + 14 * width + 12
  | .monus op => 5 * ((values op.left).size + (values op.right).size) + 7
  | .constant _ _ => 1
  | .clear dst => (values dst).size + 1
  | .copy _ src _ => 2 * ((values src).size + 1)

def budget [DecidableEq Reg] : List (Command Reg) → (Reg → Nat) → Nat :=
  MachineFiniteSequence.steps result cost

def LocalLabel : Command Reg → Type
  | .add _ => BinaryAddPreserving.Label
  | .mul _ => BinaryMulMachine.Label
  | .monus _ => BinaryMonusPreserving.Label
  | .constant _ _ | .clear _ => Unit
  | .copy _ _ _ => Bool

instance (command : Command Reg) : Fintype (LocalLabel command) := by
  cases command <;> dsimp [LocalLabel] <;> infer_instance

instance (command : Command Reg) : DecidableEq (LocalLabel command) := by
  cases command <;> dsimp [LocalLabel] <;> infer_instance

def main : (command : Command Reg) → LocalLabel command
  | .add _ => .leftOut
  | .mul _ => .copyLeft
  | .monus _ => .leftOut
  | .constant _ _ | .clear _ => ()
  | .copy _ _ _ => false

def localInstruction [DecidableEq K] (slot : (Reg ⊕ Fin 6) ↪ K) :
    (command : Command Reg) → (LocalLabel command → Λ) → Option Λ →
    LocalLabel command → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A)
  | .add op, labels, exit => BinaryAddPreserving.instruction (addSlots slot op) labels exit
  | .mul op, labels, exit => BinaryMulMachine.statement (mulSlots slot op) labels exit
  | .monus op, labels, exit => BinaryMonusPreserving.instruction (addSlots slot op) labels exit
  | .constant dst n, _, exit => fun _ =>
      MachineSubstitution.pushWord (slot (.inl dst)) n.bits.reverse
        (MachineTransfer.exitAt (slot (.inl dst)) exit)
  | .clear dst, labels, exit => fun _ =>
      MachineDrain.drain (slot (.inl dst)) (labels ()) exit
  | .copy dst src _, labels, exit => fun label =>
      bif label then
        MachineCopy.forkLoop (slot (.inr 0)) (slot (.inl src)) (slot (.inl dst))
          false (labels true) exit
      else
        MachineTransfer.loopAt (slot (.inl src)) (slot (.inr 0)) id false
          (labels false) (some (labels true))

abbrev Label (commands : List (Command Reg)) := MachineFiniteSequence.Label LocalLabel commands

def entry (commands : List (Command Reg)) (labels : Label commands → Λ) (exit : Option Λ) :=
  MachineFiniteSequence.entry LocalLabel main commands labels exit

def instruction [DecidableEq K] (slot : (Reg ⊕ Fin 6) ↪ K)
    (commands : List (Command Reg)) (labels : Label commands → Λ) (exit : Option Λ) :=
  MachineFiniteSequence.instruction LocalLabel main (localInstruction (A := A) slot)
    commands labels exit

end BinPackingGap.BinaryRegisterProgram

namespace BinPackingGap.NatExpressionCompiler

open BinaryRegisterProgram

inductive BinaryOp
  | add
  | mul
  | monus
  deriving DecidableEq

instance : Fintype BinaryOp where
  elems := {.add, .mul, .monus}
  complete op := by cases op <;> simp

def applyOp : BinaryOp → Nat → Nat → Nat
  | .add, left, right => left + right
  | .mul, left, right => left * right
  | .monus, left, right => left - right

variable {α Reg L R N : Type}

def command : BinaryOp → Operands Reg → Command Reg
  | .add, operands => .add operands
  | .mul, operands => .mul operands
  | .monus, operands => .monus operands

@[simp] theorem destination_command (op : BinaryOp) (operands : Operands Reg) :
    destination (command op operands) = operands.destination := by
  cases op <;> rfl

@[simp] theorem value_command (op : BinaryOp) (operands : Operands Reg)
    (regs : Reg → Nat) :
    value (command op operands) regs =
      applyOp op (regs operands.left) (regs operands.right) := by
  cases op <;> rfl

@[simp] theorem commandReady_command (op : BinaryOp) (operands : Operands Reg)
    (regs : Reg → Nat) :
    commandReady (command op operands) regs ↔ regs operands.destination = 0 := by
  cases op <;> rfl

def leftReg (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) : L ↪ Reg where
  toFun node := loc (.inr (.inl node))
  inj' := by
    intro a b h
    exact Sum.inl.inj (Sum.inr.inj (loc.injective h))

def rightReg (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) : R ↪ Reg where
  toFun node := loc (.inr (.inr node))
  inj' := by
    intro a b h
    exact Sum.inr.inj (Sum.inr.inj (loc.injective h))

@[simp] theorem leftReg_apply (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) (node : L) :
    leftReg loc node = loc (.inr (.inl node)) := rfl

@[simp] theorem rightReg_apply (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) (node : R) :
    rightReg loc node = loc (.inr (.inr node)) := rfl

theorem leftReg_ne_rightReg (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) (left : L) (right : R) :
    leftReg loc left ≠ rightReg loc right := by
  intro h
  change loc (.inr (.inl left)) = loc (.inr (.inr right)) at h
  have htag := loc.injective h
  cases htag

theorem root_ne_leftReg (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) (left : L) :
    loc (.inl ()) ≠ leftReg loc left := by
  intro h
  change loc (.inl ()) = loc (.inr (.inl left)) at h
  have htag := loc.injective h
  cases htag

theorem root_ne_rightReg (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) (right : R) :
    loc (.inl ()) ≠ rightReg loc right := by
  intro h
  change loc (.inl ()) = loc (.inr (.inr right)) at h
  have htag := loc.injective h
  cases htag

def branchOperands (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) (leftRoot : L) (rightRoot : R) :
    Operands Reg where
  destination := loc (.inl ())
  left := leftReg loc leftRoot
  right := rightReg loc rightRoot
  left_ne_right := leftReg_ne_rightReg loc leftRoot rightRoot
  left_ne_destination := Ne.symm (root_ne_leftReg loc leftRoot)
  right_ne_destination := Ne.symm (root_ne_rightReg loc rightRoot)

@[simp] theorem branchOperands_destination (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg)
    (leftRoot : L) (rightRoot : R) :
    (branchOperands loc leftRoot rightRoot).destination = loc (.inl ()) := rfl

@[simp] theorem branchOperands_left (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg)
    (leftRoot : L) (rightRoot : R) :
    (branchOperands loc leftRoot rightRoot).left = leftReg loc leftRoot := rfl

@[simp] theorem branchOperands_right (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg)
    (leftRoot : L) (rightRoot : R) :
    (branchOperands loc leftRoot rightRoot).right = rightReg loc rightRoot := rfl

variable [DecidableEq Reg]

@[simp] theorem result_command_destination (op : BinaryOp) (operands : Operands Reg)
    (regs : Reg → Nat) :
    result (command op operands) regs operands.destination =
      applyOp op (regs operands.left) (regs operands.right) := by
  simpa only [destination_command, value_command] using
    result_destination (command op operands) regs

def Correct (inputs : α → Reg) (nodes : N ↪ Reg) (out : N)
    (value : (α → Nat) → Nat) (commands : List (Command Reg)) : Prop :=
  ∀ regs : Reg → Nat, (∀ node, regs (nodes node) = 0) →
    Ready commands regs ∧
      resultOf commands regs (nodes out) = value (fun a => regs (inputs a)) ∧
      ∀ r, (∀ node, r ≠ nodes node) → resultOf commands regs r = regs r

theorem branchCorrect (op : BinaryOp) (inputs : α → Reg)
    (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg)
    (inputDisjoint : ∀ a node, inputs a ≠ loc node)
    (leftRoot : L) (rightRoot : R)
    (leftValue rightValue : (α → Nat) → Nat)
    (leftCommands rightCommands : List (Command Reg))
    (hLeft : Correct inputs (leftReg loc) leftRoot leftValue leftCommands)
    (hRight : Correct inputs (rightReg loc) rightRoot rightValue rightCommands) :
    Correct inputs loc (.inl ())
      (fun values => applyOp op (leftValue values) (rightValue values))
      ((leftCommands ++ rightCommands) ++
        [command op (branchOperands loc leftRoot rightRoot)]) := by
  intro regs zeroNodes
  have zeroLeft : ∀ node, regs (leftReg loc node) = 0 :=
    fun node => zeroNodes (.inr (.inl node))
  rcases hLeft regs zeroLeft with ⟨readyLeft, outputLeft, frameLeft⟩
  let middle := resultOf leftCommands regs
  have zeroRight : ∀ node, middle (rightReg loc node) = 0 := by
    intro node
    calc
      middle (rightReg loc node) = regs (rightReg loc node) :=
        frameLeft _ (fun left => Ne.symm (leftReg_ne_rightReg loc left node))
      _ = 0 := zeroNodes (.inr (.inr node))
  have inputsUnchanged : (fun a => middle (inputs a)) = (fun a => regs (inputs a)) := by
    funext a
    exact frameLeft _ (fun node => inputDisjoint a (.inr (.inl node)))
  rcases hRight middle zeroRight with ⟨readyRight, outputRight, frameRight⟩
  rw [inputsUnchanged] at outputRight
  have rootAfterLeft : middle (loc (.inl ())) = 0 := by
    calc
      middle (loc (.inl ())) = regs (loc (.inl ())) :=
        frameLeft _ (root_ne_leftReg loc)
      _ = 0 := zeroNodes (.inl ())
  have rootAfterRight : resultOf rightCommands middle (loc (.inl ())) = 0 := by
    calc
      resultOf rightCommands middle (loc (.inl ())) = middle (loc (.inl ())) :=
        frameRight _ (root_ne_rightReg loc)
      _ = 0 := rootAfterLeft
  have leftAfterRight : resultOf rightCommands middle (leftReg loc leftRoot) =
      leftValue (fun a => regs (inputs a)) := by
    calc
      resultOf rightCommands middle (leftReg loc leftRoot) =
          middle (leftReg loc leftRoot) :=
        frameRight _ (leftReg_ne_rightReg loc leftRoot)
      _ = leftValue (fun a => regs (inputs a)) := outputLeft
  have readyLast : Ready [command op (branchOperands loc leftRoot rightRoot)]
      (resultOf rightCommands middle) := by
    refine ⟨?_, trivial⟩
    simpa only [commandReady_command, branchOperands_destination] using rootAfterRight
  have finalResult : resultOf ((leftCommands ++ rightCommands) ++
      [command op (branchOperands loc leftRoot rightRoot)]) regs =
      result (command op (branchOperands loc leftRoot rightRoot))
        (resultOf rightCommands middle) := by
    simp only [resultOf_append, resultOf_cons, resultOf_nil, middle]
  refine ⟨?_, ?_, ?_⟩
  · apply (Ready_append (leftCommands ++ rightCommands)
      [command op (branchOperands loc leftRoot rightRoot)] regs).2
    refine ⟨(Ready_append leftCommands rightCommands regs).2 ⟨readyLeft, readyRight⟩, ?_⟩
    simpa only [resultOf_append] using readyLast
  · rw [finalResult]
    change result (command op (branchOperands loc leftRoot rightRoot))
      (resultOf rightCommands middle) (branchOperands loc leftRoot rightRoot).destination = _
    rw [result_command_destination]
    change applyOp op (resultOf rightCommands middle (leftReg loc leftRoot))
      (resultOf rightCommands middle (rightReg loc rightRoot)) = _
    rw [leftAfterRight, outputRight]
  · intro r outside
    rw [finalResult]
    calc
      result (command op (branchOperands loc leftRoot rightRoot))
          (resultOf rightCommands middle) r = resultOf rightCommands middle r :=
        result_other _ _ r (by
          simpa only [destination_command, branchOperands_destination] using outside (.inl ()))
      _ = middle r := frameRight _ (fun node => outside (.inr (.inr node)))
      _ = regs r := frameLeft _ (fun node => outside (.inr (.inl node)))

end BinPackingGap.NatExpressionCompiler

end OAI
