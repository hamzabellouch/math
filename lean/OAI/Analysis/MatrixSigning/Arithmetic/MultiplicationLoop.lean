import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.MultiplicationBody

namespace OAI

namespace KS.W03.MultiplicationLoop

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.MultiplicationBody KS.W03.BinaryAccumulator KS.W03.BinaryMultiply

def guard (heads : Fin 7 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 7 :=
  if (heads 1).val = 0 then
    ⟨.halt, Vector.ofFn (fun _ => .stay)⟩
  else if (heads 1).val = 1 then
    ⟨.restart, Vector.ofFn (fun j =>
      if j = 1 then .pop else if j = 2 then .push false else .stay)⟩
  else
    ⟨.call, Vector.ofFn (fun j => if j = 1 then .pop else .stay)⟩

def program : Program 7 := KS.W29.FixedLoop.loop body guard

def cfg (input xs operand acc : List Bool) : Config 7 program.states :=
  ⟨some program.initial, registers input xs operand acc [] [] []⟩

def advance : List Bool → List Bool → List Bool
  | [], operand => operand
  | _ :: xs, operand => advance xs (shift operand)

theorem advance_length (xs operand : List Bool) :
    (advance xs operand).length = xs.length + operand.length := by
  induction xs generalizing operand with
  | nil => simp [advance]
  | cons b xs ih => simp [advance, ih, Nat.add_comm, Nat.add_left_comm]

theorem step_empty (input operand acc : List Bool) (coin : Bool) :
    program.toMachine.step (cfg input [] operand acc) coin =
      ⟨none, registers input [] operand acc [] [] []⟩ := by
  change (KS.W29.FixedLoop.loop body guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body), registers input [] operand acc [] [] []⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  change Config.mk none _ = Config.mk none _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem step_false (input xs operand acc : List Bool) (coin : Bool) :
    program.toMachine.step (cfg input (false :: xs) operand acc) coin =
      cfg input xs (shift operand) acc := by
  change (KS.W29.FixedLoop.loop body guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body), registers input (false :: xs) operand acc [] [] []⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  change Config.mk (some (KS.W29.FixedLoop.guardState body)) _ =
    Config.mk (some (KS.W29.FixedLoop.guardState body)) _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem step_true (input xs operand acc : List Bool) (coin : Bool) :
    program.toMachine.step (cfg input (true :: xs) operand acc) coin =
      KS.W29.FixedLoop.liftBody body
        ⟨some body.initial, registers input xs operand acc [] [] []⟩ := by
  change (KS.W29.FixedLoop.loop body guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body), registers input (true :: xs) operand acc [] [] []⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  change Config.mk (some (KS.W29.FixedLoop.bodyState body body.initial)) _ =
    Config.mk (some (KS.W29.FixedLoop.bodyState body body.initial)) _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_loop (input xs operand acc bits : List Bool)
    (hlen : loopTicks xs operand acc ≤ bits.length) :
    program.toMachine.run (cfg input xs operand acc) bits =
      ⟨none, registers input [] (advance xs operand) (loop xs operand acc) [] [] []⟩ := by
  induction xs generalizing operand acc bits with
  | nil =>
    cases bits with
    | nil => simp [loopTicks] at hlen
    | cons coin rest =>
      erw [Machine.run.eq_2, step_empty, Machine.run_halted _ _ rfl]
      rfl
  | cons b xs ih =>
    cases bits with
    | nil => simp [loopTicks] at hlen
    | cons coin rest =>
      cases b
      · have ht : loopTicks xs (shift operand) acc ≤ rest.length := by
          simp [loopTicks, roundTicks, nextAccumulator] at hlen
          omega
        erw [Machine.run.eq_2, step_false]
        simpa [advance, loop, nextAccumulator] using
          ih (shift operand) acc rest ht
      · have ht : bodyTicks operand acc +
            loopTicks xs (shift operand) (KS.W01.BinaryAdder.addBits false acc operand) ≤ rest.length := by
          simp [loopTicks, roundTicks, nextAccumulator] at hlen
          omega
        obtain ⟨remaining, hremaining, hreturn⟩ :=
          (body_spec input xs operand acc).loop_body_then guard rest (by omega)
        erw [Machine.run.eq_2, step_true]
        erw [hreturn]
        have hn : loopTicks xs (shift operand) (KS.W01.BinaryAdder.addBits false acc operand) ≤
            remaining.length := by omega
        simp only [advance, loop, nextAccumulator]
        exact ih (shift operand) (KS.W01.BinaryAdder.addBits false acc operand) remaining hn

theorem loop_spec (input xs operand acc : List Bool) :
    RunSpec program (registers input xs operand acc [] [] [])
      (registers input [] (advance xs operand) (loop xs operand acc) [] [] [])
      (loopTicks xs operand acc) := by
  intro bits hbits
  exact run_loop input xs operand acc bits (by omega)

theorem run_product (xs operand bits : List Bool)
    (hlen : 8 * (xs.length + operand.length + 1) ^ 2 ≤ bits.length) :
    let result := program.toMachine.run (cfg [] xs operand []) bits
    result.state = none ∧
      KS.W19.bitsValue (result.«stacks» (3 : Fin 7)) = KS.W19.bitsValue xs * KS.W19.bitsValue operand ∧
      (result.«stacks» (3 : Fin 7)).length ≤ xs.length + operand.length := by
  have ht := loop_zero_ticks_le xs operand
  dsimp only
  rw [run_loop [] xs operand [] bits (ht.trans hlen)]
  exact ⟨rfl, loop_zero_correct xs operand, loop_zero_length_le xs operand⟩

theorem fixed_state_count : program.states = body.states + 1 := rfl

end KS.W03.MultiplicationLoop

end OAI
