import Mathlib
import OAI.Analysis.MatrixSigning.Machines.Sequential
import OAI.Analysis.MatrixSigning.Encoding.FrameDecoder

namespace OAI

namespace KS.W19.FrameActivity
open KS.W29 KS.W29.Sequential KS.W29.FrameDecoder

theorem activeFor_append (M : BinaryMachine) (c : Config M.states) (xs ys : List Bool) :
    ActiveFor M c (xs ++ ys) ↔ ActiveFor M c xs ∧ ActiveFor M (M.run c xs) ys := by
  induction xs generalizing c with
  | nil => simp [ActiveFor, BinaryMachine.run]
  | cons b bs ih => simp [ActiveFor, BinaryMachine.run, ih, and_assoc]

theorem active_read (payload tail output scratch bits : List Bool)
    (hlen : bits.length = 2 * payload.length + 1) :
    ActiveFor FrameDecoder.machine
      (config (some 0) (KS.W01.frame payload ++ tail) output scratch) bits := by
  induction payload generalizing scratch bits with
  | nil =>
    cases bits with
    | nil => simp at hlen
    | cons b bs =>
      have hb : bs = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons, List.length_nil] at hlen
        omega
      subst bs
      exact ⟨Option.some_ne_none _, trivial⟩
  | cons x xs ih =>
    cases bits with
    | nil => simp at hlen
    | cons b₀ bs =>
      cases bs with
      | nil => simp at hlen
      | cons b₁ rest =>
        have hr : rest.length = 2 * xs.length + 1 := by
          simp only [List.length_cons] at hlen
          omega
        change ActiveFor FrameDecoder.machine
          (config (some 0) (false :: x :: (KS.W01.frame xs ++ tail)) output scratch)
          (b₀ :: b₁ :: rest)
        refine ⟨Option.some_ne_none _, ?_⟩
        rw [tag_false_step]
        refine ⟨Option.some_ne_none _, ?_⟩
        rw [data_step]
        exact ih _ _ hr

theorem active_reverse (input output scratch bits : List Bool)
    (hlen : bits.length = scratch.length + 1) :
    ActiveFor FrameDecoder.machine (config (some 2) input output scratch) bits := by
  induction scratch generalizing output bits with
  | nil =>
    cases bits with
    | nil => simp at hlen
    | cons b bs =>
      have hb : bs = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
      subst bs
      exact ⟨Option.some_ne_none _, trivial⟩
  | cons x xs ih =>
    cases bits with
    | nil => simp at hlen
    | cons b bs =>
      have hb : bs.length = xs.length + 1 := by simpa using hlen
      refine ⟨Option.some_ne_none _, ?_⟩
      rw [reverse_step]
      exact ih _ _ hb

theorem haltsAfter_frame (payload tail bits : List Bool)
    (hlen : bits.length = 3 * payload.length + 2) :
    HaltsAfter FrameDecoder.machine (FrameDecoder.machine.init (KS.W01.frame payload ++ tail)) bits := by
  refine ⟨?_, ?_⟩
  · have hi : FrameDecoder.machine.init (KS.W01.frame payload ++ tail) =
        config (some 0) (KS.W01.frame payload ++ tail) [] [] := by
      simp [BinaryMachine.init, FrameDecoder.machine, FiniteDispatch.compile, config]
    rw [hi]
    have hl : (bits.take (2 * payload.length + 1)).length = 2 * payload.length + 1 := by
      simp only [List.length_take, hlen]
      omega
    have hr : (bits.drop (2 * payload.length + 1)).length = payload.length + 1 := by
      simp only [List.length_drop, hlen]
      omega
    rw [← List.take_append_drop (2 * payload.length + 1) bits]
    apply (activeFor_append FrameDecoder.machine
      (config (some 0) (KS.W01.frame payload ++ tail) [] [])
      (bits.take (2 * payload.length + 1)) (bits.drop (2 * payload.length + 1))).mpr
    refine ⟨active_read payload tail [] [] _ hl, ?_⟩
    rw [run_read payload tail [] [] _ hl]
    apply active_reverse
    simpa using hr
  · rw [run_frame payload tail bits hlen]
    rfl

end KS.W19.FrameActivity

end OAI
