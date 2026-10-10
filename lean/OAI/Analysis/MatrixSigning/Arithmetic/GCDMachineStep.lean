import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.DivisionLoopBridge
import OAI.Analysis.MatrixSigning.Arithmetic.GCDMachine
import OAI.Analysis.MatrixSigning.Arithmetic.DivisionLoopRun

namespace OAI

section

namespace KS.W30.GCDMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

lemma process_quotient_length (d pending q r : List Bool) :
    (DivisionLoop.process d pending q r).1.length = pending.length + q.length := by
  induction pending generalizing q r with
  | nil => simp [DivisionLoop.process]
  | cons b bs ih =>
    rw [DivisionLoop.process, ih, DivisionLoop.advance_quotient_length]
    simp only [List.length_cons]
    omega

lemma process_remainder_length (d pending q r : List Bool) (R : ℕ)
    (hr : r.length + pending.length ≤ R) (hd : d.length + pending.length ≤ R) :
    (DivisionLoop.process d pending q r).2.length ≤ R := by
  induction pending generalizing q r with
  | nil => simpa [DivisionLoop.process] using hr
  | cons b bs ih =>
    rw [DivisionLoop.process]
    apply ih
    · have h := DivisionLoop.advance_remainder_length d b q r
      simp only [List.length_cons] at hr hd
      omega
    · simp only [List.length_cons] at hd
      omega

theorem body_spec (x y : List Bool) (L : ℕ) (hx : x.length ≤ L) (hy : y.length ≤ L)
    (hyp : 0 < bitsValue y) :
    RunSpec body (state x y) (state y (trimBits (divideBits y x).2))
      (40 * (L + 1) ^ 2) := by
  let qr := DivisionLoop.process y x.reverse [] []
  have hd : RunSpec DivisionMachine.loop (state x y)
      (DivisionMachine.«stacks» y [] qr.1 qr.2 [] [] [] [])
      (x.length * (8 * (x.length + 2 * y.length + 2) + 1) + 1) := by
    intro bits hlen
    exact DivisionMachine.loop_payload y x bits (by omega)
  have hc := cleanup_spec y qr.1 qr.2
  have h := hd.compose hc
  have hq : qr.1.length = x.length := by
    simpa only [qr, List.length_reverse, List.length_nil, Nat.add_zero] using
      process_quotient_length y x.reverse [] []
  have hr : qr.2.length ≤ x.length + y.length := by
    apply process_remainder_length y x.reverse [] [] (x.length + y.length)
    · simp
    · simp; omega
  have ht : x.length * (8 * (x.length + 2 * y.length + 2) + 1) + 1 +
      (qr.1.length + y.length + 2 * qr.2.length + 4) ≤ 40 * (L + 1) ^ 2 := by
    rw [hq]
    have hm : x.length * (8 * (x.length + 2 * y.length + 2) + 1) ≤
        L * (8 * (3 * L + 2) + 1) := Nat.mul_le_mul hx (by omega)
    nlinarith
  have ho : trimBits qr.2 = trimBits (divideBits y x).2 :=
    KS.W30.BinaryRational.divisionLoop_trim_remainder y x hyp
  simpa only [body, ho] using h.mono ht

theorem guard_zero (x : List Bool) (coin : Bool) :
    loop.toMachine.step ⟨some loop.initial, state x []⟩ coin = ⟨none, state x []⟩ := by
  unfold loop
  erw [KS.W29.FixedLoop.step_guard]
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem guard_nonzero (x y : List Bool) (hy : y ≠ []) (coin : Bool) :
    loop.toMachine.step ⟨some loop.initial, state x y⟩ coin =
      KS.W29.FixedLoop.liftBody body ⟨some body.initial, state x y⟩ := by
  cases y with
  | nil => exact (hy rfl).elim
  | cons b bs =>
    unfold loop
    erw [KS.W29.FixedLoop.step_guard]
    cases b <;> apply config_ext
    all_goals first | rfl | (intro j; fin_cases j <;> rfl)

end KS.W30.GCDMachine

end

end OAI
