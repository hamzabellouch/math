import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineCombinators
import OAI.Analysis.MatrixSigning.Machines.FixedDotModel

namespace OAI

namespace KS.W12.FixedDot

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def registers (source input product accumulator temporary : List Bool) : Fin 19 → List Bool :=
  fun j => if j = 16 then source else if j = 0 then input else if j = 10 then product
    else if j = 17 then accumulator else if j = 18 then temporary else []

def boundary (source : List Bool) (a : ℚ) : Fin 19 → List Bool :=
  registers source [] [] (KS.W01.encodeRat a) []

def guard (heads : Fin 19 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 19 :=
  ⟨if (heads 16).val = 0 then .halt else .call, Vector.ofFn (fun _ => .stay)⟩

def loopProgram (body : Program 19) : Program 19 := KS.W29.FixedLoop.loop body guard

def loopConfig (body : Program 19) (source : List Bool) (a : ℚ) :
    Config 19 (loopProgram body).states :=
  ⟨some (loopProgram body).initial, boundary source a⟩

theorem step_empty (body : Program 19) (a : ℚ) (coin : Bool) :
    (loopProgram body).toMachine.step (loopConfig body [] a) coin =
      ⟨none, boundary [] a⟩ := by
  change (KS.W29.FixedLoop.loop body guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body), boundary [] a⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  change Config.mk none _ = Config.mk none _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem step_cons (body : Program 19) (b : Bool) (source : List Bool)
    (a : ℚ) (coin : Bool) :
    (loopProgram body).toMachine.step (loopConfig body (b :: source) a) coin =
      KS.W29.FixedLoop.liftBody body ⟨some body.initial, boundary (b :: source) a⟩ := by
  change (KS.W29.FixedLoop.loop body guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body), boundary (b :: source) a⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  cases b <;>
    change Config.mk (some (KS.W29.FixedLoop.bodyState body body.initial)) _ =
      Config.mk (some (KS.W29.FixedLoop.bodyState body body.initial)) _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_pair (body : Program 19) (p : ℚ × ℚ) (ps : List (ℚ × ℚ))
    (a : ℚ) (coin : Bool) :
    (loopProgram body).toMachine.step (loopConfig body (inputWire (p :: ps)) a) coin =
      KS.W29.FixedLoop.liftBody body
        ⟨some body.initial, boundary (inputWire (p :: ps)) a⟩ := by
  cases h : inputWire (p :: ps) with
  | nil => exact (inputWire_cons_nonempty p ps h).elim
  | cons b source => exact step_cons body b source a coin

def loopTicks (bodyTicks : (ℚ × ℚ) → ℚ → ℕ) : List (ℚ × ℚ) → ℚ → ℕ
  | [], _ => 1
  | p :: ps, a => 1 + bodyTicks p a + loopTicks bodyTicks ps (a + p.1 * p.2)

theorem run_loop_of_body_spec (body : Program 19) (bodyTicks : (ℚ × ℚ) → ℚ → ℕ)
    (hbody : ∀ p ps a, RunSpec body (boundary (inputWire (p :: ps)) a)
      (boundary (inputWire ps) (a + p.1 * p.2)) (bodyTicks p a))
    (ps : List (ℚ × ℚ)) (a : ℚ) (bits : List Bool)
    (hlen : loopTicks bodyTicks ps a ≤ bits.length) :
    (loopProgram body).toMachine.run (loopConfig body (inputWire ps) a) bits =
      ⟨none, boundary [] (a + dotValue ps)⟩ := by
  induction ps generalizing a bits with
  | nil =>
      cases bits with
      | nil => simp [loopTicks] at hlen
      | cons coin rest =>
          simp only [inputWire_nil, dotValue_nil, add_zero]
          erw [Machine.run.eq_2, step_empty, Machine.run_halted _ _ rfl]
  | cons p ps ih =>
      cases bits with
      | nil => simp [loopTicks] at hlen
      | cons coin rest =>
          have ht : bodyTicks p a + loopTicks bodyTicks ps (a + p.1 * p.2) ≤ rest.length := by
            simp only [loopTicks, List.length_cons] at hlen
            omega
          obtain ⟨remaining, hremaining, hreturn⟩ :=
            (hbody p ps a).loop_body_then guard rest (by omega)
          erw [Machine.run.eq_2, step_pair]
          change (loopProgram body).toMachine.run
              (KS.W29.FixedLoop.liftBody body
                ⟨some body.initial, boundary (inputWire (p :: ps)) a⟩) rest =
            (loopProgram body).toMachine.run
              (loopConfig body (inputWire ps) (a + p.1 * p.2)) remaining at hreturn
          rw [hreturn]
          have hn : loopTicks bodyTicks ps (a + p.1 * p.2) ≤ remaining.length := by omega
          simpa only [loopConfig, loopProgram, KS.W29.FixedLoop.loop_initial,
            accumulator_step] using ih (a + p.1 * p.2) remaining hn

theorem transient_stack_bound (body : Program 19) (source : List Bool) (a : ℚ)
    (bits : List Bool) (j : Fin 19) :
    (((loopProgram body).toMachine.run (loopConfig body source a) bits).«stacks» j).length ≤
      source.length + (KS.W01.encodeRat a).length + bits.length := by
  have h := (loopProgram body).toMachine.run_stack_length_le (loopConfig body source a) bits j
  have hb : ((boundary source a) j).length ≤ source.length + (KS.W01.encodeRat a).length := by
    fin_cases j <;> simp [boundary, registers]
  exact h.trans (Nat.add_le_add_right hb _)

theorem loop_table_length (body : Program 19) :
    (loopProgram body).table.length = (body.states + 1) * (3 ^ 19 * 2) :=
  KS.W29.FixedLoop.loop_table_length body guard

end KS.W12.FixedDot

end OAI
