import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RowDotBody

namespace OAI

section

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def guard (heads : Fin 29 → Fin 3) (_ : Bool) : KS.W29.FixedLoop.GuardInstruction 29 :=
  ⟨if (heads 23).val = 0 then .halt else .call, Vector.ofFn (fun _ => .stay)⟩
def loopProgram : Program 29 := KS.W29.FixedLoop.loop body guard

def loopTicks {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ) (i : Fin n) :
    List (Fin n × ℚ) → ℕ
  | [] => 1
  | p :: ps => 1 + bodyTicks M b i p + loopTicks M b i ps

theorem step_empty {n : ℕ} (M : KS.W07.DenseRatMatrix n) (x : Fin n → ℚ)
    (i : Fin n) (k : ℕ) (out : List Bool) (coin : Bool) :
    loopProgram.toMachine.step ⟨some loopProgram.initial, boundary M x i [] k out⟩ coin =
      ⟨none, boundary M x i [] k out⟩ := by
  change (KS.W29.FixedLoop.loop body guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body), boundary M x i [] k out⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  change Config.mk none _ = Config.mk none _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem step_cons {n : ℕ} (M : KS.W07.DenseRatMatrix n) (x : Fin n → ℚ)
    (i : Fin n) (p : Fin n × ℚ) (xs : List (Fin n × ℚ)) (k : ℕ)
    (out : List Bool) (coin : Bool) :
    loopProgram.toMachine.step ⟨some loopProgram.initial, boundary M x i (p :: xs) k out⟩ coin =
      KS.W29.FixedLoop.liftBody body ⟨some body.initial, boundary M x i (p :: xs) k out⟩ := by
  change (KS.W29.FixedLoop.loop body guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body), boundary M x i (p :: xs) k out⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  have hhead : KS.W29.topCode ((boundary M x i (p :: xs) k out) 23) ≠ 0 := by
    change KS.W29.topCode (KS.W01.frame (KS.W01.encodeRat p.2) ++ tailTape xs) ≠ 0
    cases hp : KS.W01.encodeRat p.2 with
    | nil => simp [KS.W01.frame, KS.W29.topCode]
    | cons b bs => simp [KS.W01.frame, KS.W29.topCode]
  simp only [guard, observedHeads, hhead, ↓reduceIte]
  change Config.mk (some (KS.W29.FixedLoop.bodyState body body.initial)) _ =
    Config.mk (some (KS.W29.FixedLoop.bodyState body body.initial)) _
  congr 1
  funext j
  simp [KS.W29.FixedLoop.guardInstruction, Instruction.action, KS.W29.StackAction.apply]

theorem run_loop {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (x : Fin n → ℚ) (i : Fin n) (xs : List (Fin n × ℚ)) (k : ℕ)
    (hc : Consecutive k xs) (out bits : List Bool) (hlen : loopTicks M b i xs ≤ bits.length) :
    loopProgram.toMachine.run ⟨some loopProgram.initial, boundary M x i xs k out⟩ bits =
      ⟨none, boundary M x i [] (k + xs.length)
        ((FixedDot.inputWire (rowPairs M i xs)).reverse ++ out)⟩ := by
  induction xs generalizing k out bits with
  | nil =>
      cases bits with
      | nil => simp [loopTicks] at hlen
      | cons coin rest =>
          rw [Machine.run, step_empty, Machine.run_halted _ _ rfl]
          simp
  | cons p xs ih =>
      obtain ⟨hk, htail⟩ := (consecutive_cons k p xs).mp hc
      subst k
      cases bits with
      | nil => simp [loopTicks] at hlen
      | cons coin rest =>
          have ht : bodyTicks M b i p + loopTicks M b i xs ≤ rest.length := by
            simp only [loopTicks, List.length_cons] at hlen
            omega
          obtain ⟨remaining, hremaining, hreturn⟩ :=
            (body_spec M b hnum hden x i p xs out).loop_body_then guard rest (by omega)
          rw [Machine.run, step_cons]
          change loopProgram.toMachine.run
              (KS.W29.FixedLoop.liftBody body
                ⟨some body.initial, boundary M x i (p :: xs) p.1.val out⟩) rest =
            loopProgram.toMachine.run
              ⟨some loopProgram.initial, boundary M x i xs (p.1.val + 1)
                ((FixedDot.pairWire (KS.W07.DenseRatMatrix.decode M i p.1, p.2)).reverse ++ out)⟩
              remaining at hreturn
          rw [hreturn]
          have hn : loopTicks M b i xs ≤ remaining.length := by omega
          simpa [loopProgram, KS.W29.FixedLoop.loop_initial, FixedDot.inputWire_cons,
            List.reverse_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
            ih (p.1.val + 1) htail
              ((FixedDot.pairWire (KS.W07.DenseRatMatrix.decode M i p.1, p.2)).reverse ++ out)
              remaining hn

theorem loop_spec {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (x : Fin n → ℚ) (i : Fin n) :
    RunSpec loopProgram (boundary M x i (indexedVector x) 0 [])
      (boundary M x i [] n ((FixedDot.inputWire (rowPairs M i (indexedVector x))).reverse))
      (loopTicks M b i (indexedVector x)) := by
  intro bits hbits
  simpa [indexedVector] using run_loop M b hnum hden x i (indexedVector x) 0
    (consecutive_indexedVector x) [] bits hbits.ge

end KS.W12.RowDot

end

end OAI
