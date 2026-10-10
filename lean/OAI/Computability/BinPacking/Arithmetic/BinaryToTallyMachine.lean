import Mathlib.Tactic.Linarith
import OAI.Computability.BinPacking.Arithmetic.NatExpressionBounds
import OAI.Computability.BinPacking.Machines.FrameEmitMachine
import OAI.Computability.BinPacking.Machines.PackingPowerProgram

namespace OAI

noncomputable section

namespace BinPackingGap.BinaryRegisterStructured

open Turing BinPackingGames.Foundations.Complexity
open BinaryRegisterProgram FiniteTapeProgram

variable {Reg K A : Type} [DecidableEq Reg] [DecidableEq K]

def code (slot : (Reg ⊕ Fin 6) ↪ K) :
    List (Command Reg) → Code (K := K) (S := BinaryAddMachine.State A)
  | [] => .atom .done
  | command :: tail =>
    .seq (.routine (LocalLabel command) inferInstance (main command)
      (localInstruction slot command id none)) (code slot tail)

theorem exec (slot : (Reg ⊕ Fin 6) ↪ K) (commands : List (Command Reg))
    (base : K → List Bool) (values : Reg → Nat) (ready : Ready commands values)
    (ambient : A) :
    ∃ steps ≤ budget commands values + 1,
      Exec (code slot commands)
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base values⟩ steps
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base (resultOf commands values)⟩ := by
  induction commands generalizing values with
  | nil => exact ⟨1, Nat.le_refl _, Exec.atom .done _⟩
  | cons command tail ih =>
    let run := commandInTime slot command id none (localInstruction slot command id none)
      (fun _ => rfl) base values ready.1 ambient
    obtain ⟨n, hn, htail⟩ := ih (result command values) ready.2
    refine ⟨run.steps + n, ?_, ?_⟩
    · have hr := run.steps_le_m
      change run.steps + n ≤ cost command values + budget tail (result command values) + 1
      omega
    · have head : Exec (.routine (LocalLabel command) inferInstance (main command)
          (localInstruction slot command id none))
          ⟨BinaryAddMachine.clean ambient, registerTapes slot base values⟩ run.steps
          ⟨BinaryAddMachine.clean ambient, registerTapes slot base (result command values)⟩ := by
        refine Exec.routine inferInstance (main command)
          (localInstruction slot command id none) _ _ run.steps ?_
        have trace := run.evals_in_steps
        change (MachineComposition.advance (TM2.step
          (localInstruction (A := A) slot command id none)))^[run.steps]
          (some (⟨some (main command), BinaryAddMachine.clean ambient,
            registerTapes slot base values⟩ : TM2.Cfg (fun _ : K => Bool)
              (LocalLabel command) (BinaryAddMachine.State A))) =
          some ⟨none, BinaryAddMachine.clean ambient,
            registerTapes slot base (result command values)⟩ at trace
        exact trace
      exact Exec.seq head htail

theorem exec_polynomial (slot : (Reg ⊕ Fin 6) ↪ K) (commands : List (Command Reg))
    (base : K → List Bool) (values : Reg → Nat) (ready : Ready commands values)
    (ambient : A) (width : Nat) (hwidth : ∀ r, (values r).size ≤ width) :
    ∃ steps ≤ (runtimePolynomial commands).eval width + 1,
      Exec (code slot commands)
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base values⟩ steps
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base (resultOf commands values)⟩ := by
  obtain ⟨n, hn, hrun⟩ := exec slot commands base values ready ambient
  refine ⟨n, hn.trans ?_, hrun⟩
  rw [runtimePolynomial_eval]
  exact Nat.add_le_add_right
    (budget_le commands values (staticWidth commands width)
      (bitBounded_from_input commands values width hwidth)) 1

theorem final_width (commands : List (Command Reg)) (values : Reg → Nat)
    (width : Nat) (hwidth : ∀ r, (values r).size ≤ width) :
    ∀ r, (resultOf commands values r).size ≤ staticWidth commands width := by
  have hb := bitBounded_from_input commands values width hwidth
  generalize hw : staticWidth commands width = bound at hb ⊢
  clear hw hwidth
  induction commands generalizing values with
  | nil => exact hb
  | cons command tail ih => exact ih (result command values) hb.2

end BinPackingGap.BinaryRegisterStructured

namespace BinPackingGap.RegisterFrameEmission

open Turing BinPackingGames.Foundations.Complexity
open BinaryRegisterProgram FiniteTapeProgram
open BinPackingGames.Reduction.MachineTransfer

variable {Reg K A : Type} [DecidableEq Reg] [DecidableEq K]

omit [DecidableEq Reg] in
theorem external_update (slot : (Reg ⊕ Fin 6) ↪ K) (base : K → List Bool)
    (values : Reg → Nat) (output : K) (outside : ∀ i, slot i ≠ output) (word : List Bool) :
    registerTapes slot (Function.update base output word) values =
      Function.update (registerTapes slot base values) output word := by
  classical
  funext k
  by_cases hk : k = output
  · subst k
    have ho : ¬ ∃ i, slot i = output := by rintro ⟨i, hi⟩; exact outside i hi
    simp [registerTapes_other slot _ values output ho]
  · by_cases hs : ∃ i, slot i = k
    · obtain ⟨i, rfl⟩ := hs
      simp [outside i]
    · simp only [registerTapes_other slot _ values k hs, Function.update_of_ne hk]

def code (source output : K) : Code (K := K) (S := BinaryAddMachine.State A) :=
  .routine Unit inferInstance ()
    (fun _ => FrameEmitMachine.instruction source output () none)

theorem exec (slot : (Reg ⊕ Fin 6) ↪ K) (base : K → List Bool) (values : Reg → Nat)
    (r : Reg) (output : K) (outside : ∀ i, slot i ≠ output) (ambient : A) :
    Exec (code (slot (.inl r)) output)
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base values⟩
      ((values r).size + 1)
      ⟨BinaryAddMachine.clean ambient,
        registerTapes slot (Function.update base output
          ((BinaryEncoding.natBits (values r)).reverse ++ base output))
          (Function.update values r 0)⟩ := by
  classical
  let current := registerTapes slot base values
  have hout : current output = base output := by
    apply registerTapes_other
    rintro ⟨i, hi⟩
    exact outside i hi
  have hsrc : current (slot (.inl r)) = (values r).bits := registerTapes_reg _ _ _ _
  have initial_eq : tapesAt (slot (.inl r)) output current (values r).bits (base output) = current := by
    rw [← hsrc, ← hout]
    exact tapesAt_self _ _ _
  have clear_eq : Function.update current (slot (.inl r)) [] =
      registerTapes slot base (Function.update values r 0) := by
    simpa only [current, Nat.zero_bits] using registerTapes_update slot base values r 0
  have final_eq : tapesAt (slot (.inl r)) output current []
      ((BinaryEncoding.natBits (values r)).reverse ++ base output) =
      registerTapes slot (Function.update base output
        ((BinaryEncoding.natBits (values r)).reverse ++ base output))
        (Function.update values r 0) := by
    rw [tapesAt, clear_eq, external_update slot base _ output outside]
  refine Exec.routine inferInstance ()
    (fun _ => FrameEmitMachine.instruction (slot (.inl r)) output () none)
    ⟨BinaryAddMachine.clean ambient, registerTapes slot base values⟩
    ⟨BinaryAddMachine.clean ambient,
      registerTapes slot (Function.update base output
        ((BinaryEncoding.natBits (values r)).reverse ++ base output))
        (Function.update values r 0)⟩ ((values r).size + 1) ?_
  have run := FrameEmitMachine.trace (A := (A × Bool) × Option Bool) (slot (.inl r)) output (outside (.inl r)) () none
    (fun _ : Unit => FrameEmitMachine.instruction (slot (.inl r)) output () none)
    rfl current ((ambient, false), none) (values r).bits (base output)
  change (BinPackingGames.Foundations.Complexity.MachineComposition.advance
    (Turing.TM2.step (fun _ : Unit =>
      FrameEmitMachine.instruction (slot (.inl r)) output () none)))^[(values r).bits.length + 1]
    (some (⟨some (), BinaryAddMachine.clean ambient,
      tapesAt (slot (.inl r)) output current (values r).bits (base output)⟩ :
        Turing.TM2.Cfg (fun _ : K => Bool) Unit (BinaryAddMachine.State A))) =
    some ⟨none, BinaryAddMachine.clean ambient,
      tapesAt (slot (.inl r)) output current []
        ((BinaryEncoding.natBits (values r)).reverse ++ base output)⟩ at run
  rw [Nat.size_eq_bits_len, initial_eq, final_eq] at run
  exact run

end BinPackingGap.RegisterFrameEmission

namespace BinPackingGap.BinaryToTallyMachine

open BinPackingGames.Foundations.Complexity BinaryRegisterProgram FiniteTapeProgram

inductive Reg
  | source | counter | one | temporary
  deriving DecidableEq

instance : Fintype Reg where
  elems := {.source, .counter, .one, .temporary}
  complete r := by cases r <;> simp

abbrev State (A : Type) := BinaryAddMachine.State A

def initial (n : Nat) : Reg → Nat
  | .source => n
  | _ => 0

def running (n remaining : Nat) : Reg → Nat
  | .source => n
  | .counter => remaining
  | .one => 1
  | .temporary => 0

def subtractOperands : Operands Reg where
  destination := .temporary
  left := .counter
  right := .one
  left_ne_right := by decide
  left_ne_destination := by decide
  right_ne_destination := by decide

def prepareCommands : List (Command Reg) :=
  [.copy .counter .source (by decide), .constant .one 1]

def decrementCommands : List (Command Reg) :=
  [.monus subtractOperands, .clear .counter,
    .copy .counter .temporary (by decide), .clear .temporary]

def finishCommands : List (Command Reg) := [.clear .one]

theorem prepare_ready (n : Nat) : Ready prepareCommands (initial n) := by
  simp [prepareCommands, Ready, commandReady, result, destination, value, initial]

theorem prepare_result (n : Nat) :
    resultOf prepareCommands (initial n) = running n n := by
  funext r
  cases r <;> simp [prepareCommands, resultOf, MachineFiniteSequence.resultOf,
    result, destination, value, initial, running]

theorem prepare_budget (n : Nat) :
    budget prepareCommands (initial n) + 1 = 2 * n.size + 4 := by
  simp [prepareCommands, budget, MachineFiniteSequence.steps, cost, initial]
  omega

theorem decrement_ready (n r : Nat) : Ready decrementCommands (running n (r + 1)) := by
  simp [decrementCommands, Ready, commandReady, result, destination, value,
    subtractOperands, running]

theorem decrement_result (n r : Nat) :
    resultOf decrementCommands (running n (r + 1)) = running n r := by
  funext q
  cases q <;> simp [decrementCommands, resultOf, MachineFiniteSequence.resultOf,
    result, destination, value, subtractOperands, running]

theorem decrement_budget (n r : Nat) :
    budget decrementCommands (running n (r + 1)) + 1 =
      6 * (r + 1).size + 3 * r.size + 17 := by
  simp [decrementCommands, budget, MachineFiniteSequence.steps, cost, result,
    destination, value, subtractOperands, running, Nat.size_one]
  omega

theorem finish_ready (n : Nat) : Ready finishCommands (running n 0) := by
  simp [finishCommands, Ready, commandReady]

theorem finish_result (n : Nat) :
    resultOf finishCommands (running n 0) = initial n := by
  funext r
  cases r <;> simp [finishCommands, resultOf, MachineFiniteSequence.resultOf,
    result, destination, value, running, initial]

theorem finish_budget (n : Nat) : budget finishCommands (running n 0) + 1 = 3 := by
  simp [finishCommands, budget, MachineFiniteSequence.steps, cost, running, Nat.size_one]

variable {K A : Type} [DecidableEq K]

def guard (slot : (Reg ⊕ Fin 6) ↪ K) : Action K (State A) :=
  .peek (slot (.inl .counter)) (fun s head => (s.1, head)) .done

def more (s : State A) : Bool := s.2.isSome

def reset : Action K (State A) :=
  .load (fun s => BinaryAddMachine.clean s.1.1.1) .done

def body (slot : (Reg ⊕ Fin 6) ↪ K) (output : K) : Code (K := K) (S := State A) :=
  .seq (.atom reset) (.seq (BinaryRegisterStructured.code slot decrementCommands)
    (.atom (.push output (fun _ => true) .done)))

def loop (slot : (Reg ⊕ Fin 6) ↪ K) (output : K) : Code (K := K) (S := State A) :=
  .loop (guard slot) more (body slot output)

def code (slot : (Reg ⊕ Fin 6) ↪ K) (output : K) : Code (K := K) (S := State A) :=
  .seq (BinaryRegisterStructured.code slot prepareCommands)
    (.seq (loop slot output) (BinaryRegisterStructured.code slot finishCommands))

private theorem bits_succ_nonempty (r : Nat) : (r + 1).bits ≠ [] := by
  intro h
  have hv := congrArg BinaryArithmetic.bitValue h
  simp only [BinaryArithmetic.bitValue_bits, BinaryArithmetic.bitValue_nil] at hv
  omega

theorem guard_more (slot : (Reg ⊕ Fin 6) ↪ K) (base : K → List Bool)
    (n r : Nat) (ambient : A) :
    more ((guard slot).eval
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n (r + 1))⟩).state =
      true := by
  have h := bits_succ_nonempty r
  simp only [guard, Action.eval, registerTapes_reg, running, more]
  cases hb : (r + 1).bits with
  | nil => exact False.elim (h hb)
  | cons b bs => rfl

theorem guard_zero (slot : (Reg ⊕ Fin 6) ↪ K) (base : K → List Bool)
    (n : Nat) (ambient : A) :
    (guard slot).eval
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n 0)⟩ =
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n 0)⟩ := by
  simp [guard, Action.eval, running, BinaryAddMachine.clean, BinaryAddMachine.state]

theorem registerTapes_update_external (slot : (Reg ⊕ Fin 6) ↪ K) (output : K)
    (outside : ∀ q, slot q ≠ output) (base : K → List Bool)
    (values : Reg → Nat) (word : List Bool) :
    Function.update (registerTapes slot base values) output word =
      registerTapes slot (Function.update base output word) values := by
  funext k
  by_cases hk : ∃ q, slot q = k
  · obtain ⟨q, rfl⟩ := hk
    simp [outside q]
  · by_cases hko : k = output
    · subst k
      simp [registerTapes_other slot _ _ _ hk]
    · simp [hko, registerTapes_other slot _ _ _ hk]

theorem body_exec (slot : (Reg ⊕ Fin 6) ↪ K) (output : K)
    (outside : ∀ q, slot q ≠ output) (base : K → List Bool)
    (n r : Nat) (ambient : A) :
    ∃ steps ≤ 6 * (r + 1).size + 3 * r.size + 19,
      Exec (body slot output)
        ((guard slot).eval
          ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n (r + 1))⟩)
        steps
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot (Function.update base output (true :: base output)) (running n r)⟩ := by
  obtain ⟨t, ht, run⟩ := BinaryRegisterStructured.exec slot decrementCommands base
    (running n (r + 1)) (decrement_ready n r) ambient
  rw [decrement_result] at run
  rw [decrement_budget] at ht
  have hreset : reset.eval ((guard slot).eval
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n (r + 1))⟩) =
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n (r + 1))⟩ := by
    rfl
  have houtput : registerTapes slot base (running n r) output = base output :=
    registerTapes_other slot base _ output (by simpa only [not_exists] using outside)
  have hpushed : (.push output (fun _ : State A => true) .done : Action K (State A)).eval
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n r)⟩ =
      ⟨BinaryAddMachine.clean ambient,
        registerTapes slot (Function.update base output (true :: base output)) (running n r)⟩ := by
    simp only [Action.eval, houtput, registerTapes_update_external slot output outside]
  refine ⟨1 + (t + 1), by omega, ?_⟩
  apply Exec.seq (Exec.atom reset _)
  rw [hreset]
  exact Exec.seq run (by
    simpa only [hpushed] using
      (Exec.atom (.push output (fun _ : State A => true) .done)
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n r)⟩))

private theorem replicate_append_true (r : Nat) (suffix : List Bool) :
    List.replicate r true ++ true :: suffix = List.replicate (r + 1) true ++ suffix := by
  induction r with
  | zero => rfl
  | succ r ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (true :: ·) ih

theorem loop_exec (slot : (Reg ⊕ Fin 6) ↪ K) (output : K)
    (outside : ∀ q, slot q ≠ output) (base : K → List Bool)
    (n r width : Nat) (bounded : r.size ≤ width) (ambient : A) :
    ∃ steps ≤ r * (9 * width + 20) + 1,
      Exec (loop slot output)
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n r)⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot (Function.update base output (List.replicate r true ++ base output))
            (running n 0)⟩ := by
  revert bounded
  induction r generalizing base with
  | zero =>
      intro _
      refine ⟨1, by simp, ?_⟩
      have h : more ((guard slot).eval
          ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n 0)⟩).state =
          false := by rw [guard_zero]; rfl
      simpa only [loop, guard_zero, List.replicate_zero, List.nil_append,
        Function.update_eq_self] using (Exec.loop_false (a := body slot output) h)
  | succ r ih =>
      intro bounded
      have hsmall := (Nat.size_le_size (Nat.le_succ r)).trans bounded
      obtain ⟨b, hb, bodyRun⟩ := body_exec slot output outside base n r ambient
      obtain ⟨t, ht, tailRun⟩ := ih (Function.update base output (true :: base output)) hsmall
      have hfinal : Function.update (Function.update base output (true :: base output)) output
          (List.replicate r true ++
            Function.update base output (true :: base output) output) =
          Function.update base output (List.replicate (r + 1) true ++ base output) := by
        simp only [Function.update_self, Function.update_idem, replicate_append_true]
      rw [hfinal] at tailRun
      refine ⟨b + t + 1, ?_, ?_⟩
      · have hs := Nat.size_le_size (Nat.le_succ r)
        nlinarith
      · exact Exec.loop_true (guard_more slot base n r ambient) bodyRun tailRun

def runtimeBound (n : Nat) : Nat := 40 * (n + 1) * (n.size + 1) ^ 2

theorem exec (slot : (Reg ⊕ Fin 6) ↪ K) (output : K)
    (outside : ∀ q, slot q ≠ output) (base : K → List Bool)
    (n : Nat) (ambient : A) :
    ∃ steps ≤ runtimeBound n,
      Exec (code slot output)
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base (initial n)⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot (Function.update base output (List.replicate n true ++ base output))
            (initial n)⟩ := by
  obtain ⟨p, hp, prepareRun⟩ := BinaryRegisterStructured.exec slot prepareCommands base
    (initial n) (prepare_ready n) ambient
  rw [prepare_result] at prepareRun
  rw [prepare_budget] at hp
  obtain ⟨l, hl, loopRun⟩ := loop_exec slot output outside base n n n.size le_rfl ambient
  obtain ⟨f, hf, finishRun⟩ := BinaryRegisterStructured.exec slot finishCommands
    (Function.update base output (List.replicate n true ++ base output))
    (running n 0) (finish_ready n) ambient
  rw [finish_result] at finishRun
  rw [finish_budget] at hf
  refine ⟨p + (l + f), ?_, Exec.seq prepareRun (Exec.seq loopRun finishRun)⟩
  have hlinear : p + (l + f) ≤ 2 * n.size + n * (9 * n.size + 20) + 8 := by omega
  have hfactor : 2 * n.size + n * (9 * n.size + 20) + 8 ≤
      (n + 1) * (9 * n.size + 20) := by nlinarith
  have hcoefficient : 9 * n.size + 20 ≤ 40 * (n.size + 1) ^ 2 := by nlinarith
  have hmul := Nat.mul_le_mul_left (n + 1) hcoefficient
  apply (hlinear.trans hfactor).trans
  simpa only [runtimeBound, Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using hmul

theorem exec_from_tapes (slot : (Reg ⊕ Fin 6) ↪ K) (output : K)
    (outside : ∀ q, slot q ≠ output) (base : K → List Bool) (n : Nat)
    (registers : ∀ r, base (slot (.inl r)) = (initial n r).bits)
    (scratch : ∀ j, base (slot (.inr j)) = []) (ambient : A) :
    ∃ steps ≤ runtimeBound n,
      Exec (code slot output) ⟨BinaryAddMachine.clean ambient, base⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          Function.update base output (List.replicate n true ++ base output)⟩ := by
  have hframe : registerTapes slot base (initial n) = base := by
    funext k
    by_cases hk : ∃ q, slot q = k
    · obtain ⟨q, rfl⟩ := hk
      cases q with
      | inl r => simpa only [registerTapes_reg] using (registers r).symm
      | inr j => simpa only [registerTapes_scratch] using (scratch j).symm
    · exact registerTapes_other slot base _ k hk
  obtain ⟨t, ht, run⟩ := exec slot output outside base n ambient
  rw [← registerTapes_update_external slot output outside, hframe] at run
  exact ⟨t, ht, run⟩

end BinPackingGap.BinaryToTallyMachine

end

end OAI
