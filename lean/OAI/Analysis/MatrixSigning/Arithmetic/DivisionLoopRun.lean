import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.DivisionBodyTime

namespace OAI

section

namespace KS.W19.DivisionMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun

theorem guard_cons (d pending q r : List Bool) (b coin : Bool) :
    loop.toMachine.step ⟨some loop.initial, «stacks» d (b :: pending) q r [] [] [] []⟩ coin =
      KS.W29.FixedLoop.liftBody body
        ⟨some body.initial, «stacks» d pending q (b :: r) [] [] [] []⟩ := by
  unfold loop
  erw [KS.W29.FixedLoop.step_guard]
  cases b <;> apply config_ext
  all_goals
    first | rfl | (intro j; fin_cases j <;> rfl)

theorem guard_nil (d q r : List Bool) (coin : Bool) :
    loop.toMachine.step ⟨some loop.initial, «stacks» d [] q r [] [] [] []⟩ coin =
      ⟨none, «stacks» d [] q r [] [] [] []⟩ := by
  unfold loop
  erw [KS.W29.FixedLoop.step_guard]
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem loop_run (d pending q r bits : List Bool) (R : Nat)
    (hr : r.length + pending.length ≤ R) (hd : d.length + pending.length ≤ R)
    (hb : pending.length * (8 * (R + d.length + 2) + 1) + 1 ≤ bits.length) :
    loop.toMachine.run ⟨some loop.initial, «stacks» d pending q r [] [] [] []⟩ bits =
      ⟨none, «stacks» d [] (DivisionLoop.process d pending q r).1
        (DivisionLoop.process d pending q r).2 [] [] [] []⟩ := by
  induction pending generalizing q r bits with
  | nil =>
    cases bits with
    | nil => simp at hb
    | cons coin tail =>
      rw [Machine.run, guard_nil, loop.toMachine.run_halted _ rfl tail]
      rfl
  | cons b bs ih =>
    cases bits with
    | nil => simp at hb
    | cons coin tail =>
      let B := 8 * (R + d.length + 2)
      have ht : B ≤ tail.length := by
        simp only [List.length_cons] at hb
        dsimp [B]
        nlinarith
      have hsmall : 8 * ((b :: r).length + d.length + 1) ≤ B := by
        simp only [List.length_cons] at hr ⊢
        dsimp [B]
        omega
      have hhalt := haltsFromWithin_mono body
        ⟨some body.initial, «stacks» d bs q (b :: r) [] [] [] []⟩
        (body_halts_linear d bs q (b :: r)) hsmall
      obtain ⟨first, rest, he, hfirst, _, hrun⟩ :=
        KS.W29.FixedLoop.run_body_within body guard
          ⟨some body.initial, «stacks» d bs q (b :: r) [] [] [] []⟩ B hhalt tail ht
      have htake : (tail.take B).length = B := by simp [List.length_take, Nat.min_eq_left ht]
      have hout := body_run_of_length_ge d bs q (b :: r) (tail.take B)
        (by rw [htake]; exact (bodyFuel_linear d (b :: r)).trans hsmall)
      have hrest : bs.length * (8 * (R + d.length + 2) + 1) + 1 ≤ rest.length := by
        have hh := congrArg List.length he
        simp only [List.length_append] at hh
        simp only [List.length_cons] at hb
        dsimp [B] at hfirst
        nlinarith
      have hnr : (DivisionLoop.advance d b q r).2.length + bs.length ≤ R := by
        have hlen := DivisionLoop.advance_remainder_length d b q r
        simp only [List.length_cons] at hr hd
        omega
      have hnd : d.length + bs.length ≤ R := by
        simp only [List.length_cons] at hd
        omega
      rw [Machine.run, guard_cons]
      change (KS.W29.FixedLoop.loop body guard).toMachine.run _ tail = _
      erw [hrun, hout]
      change loop.toMachine.run
        ⟨some loop.initial, «stacks» d bs (trialResult d q (b :: r)).1
          (trialResult d q (b :: r)).2 [] [] [] []⟩ rest = _
      rw [trialResult_advance]
      simpa only [DivisionLoop.process] using
        ih (DivisionLoop.advance d b q r).1 (DivisionLoop.advance d b q r).2 rest hnr hnd hrest

theorem loop_payload (d xs bits : List Bool)
    (hb : xs.length * (8 * (xs.length + 2 * d.length + 2) + 1) + 1 ≤ bits.length) :
    loop.toMachine.run ⟨some loop.initial, «stacks» d xs.reverse [] [] [] [] [] []⟩ bits =
      ⟨none, «stacks» d [] (DivisionLoop.process d xs.reverse [] []).1
        (DivisionLoop.process d xs.reverse [] []).2 [] [] [] []⟩ := by
  apply loop_run d xs.reverse [] [] bits (xs.length + d.length)
  · simp
  · simp; omega
  · simpa only [List.length_reverse, Nat.add_assoc, two_mul] using hb

theorem loop_payload_correct (d xs bits : List Bool) (hd : 0 < bitsValue d)
    (hb : xs.length * (8 * (xs.length + 2 * d.length + 2) + 1) + 1 ≤ bits.length) :
    let result := loop.toMachine.run ⟨some loop.initial, «stacks» d xs.reverse [] [] [] [] [] []⟩ bits
    result.state = none ∧ result.«stacks» (2 : Fin 10) = d ∧ result.«stacks» (3 : Fin 10) = [] ∧
      bitsValue xs = bitsValue d * bitsValue (result.«stacks» (5 : Fin 10)) + bitsValue (result.«stacks» (4 : Fin 10)) ∧
      bitsValue (result.«stacks» (4 : Fin 10)) < bitsValue d := by
  dsimp only
  erw [loop_payload d xs bits hb]
  have h := DivisionLoop.process_payload_correct d xs hd
  exact ⟨rfl, rfl, rfl, h.1, h.2⟩

end KS.W19.DivisionMachine

end

end OAI
