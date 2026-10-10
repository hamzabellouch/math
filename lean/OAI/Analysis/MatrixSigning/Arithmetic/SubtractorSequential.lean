import Mathlib
import OAI.Analysis.MatrixSigning.Machines.Sequential
import OAI.Analysis.MatrixSigning.Machines.EntryPoint
import OAI.Analysis.MatrixSigning.Encoding.FrameDecoder
import OAI.Analysis.MatrixSigning.Arithmetic.BinarySubtractor

namespace OAI

namespace KS.W19.BinarySubtractor
open KS.W29
open KS.W29.Sequential

theorem activeFor_sub (c : Bool) (xs ys zs bits : List Bool)
    (hlen : bits.length = max xs.length ys.length + 1) :
    ActiveFor machine (cfg (some (borrowState c)) xs ys zs) bits := by
  induction xs generalizing c ys zs bits with
  | nil =>
    induction ys generalizing c zs bits with
    | nil =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
        have hr : rest = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons, List.length_nil, max_self] at hlen
          omega
        subst rest
        exact ⟨Option.some_ne_none _, trivial⟩
    | cons b ys ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
        have hr : rest.length = max ([] : List Bool).length ys.length + 1 := by
          simp only [List.length_cons, List.length_nil, Nat.zero_max] at hlen ⊢
          omega
        refine ⟨Option.some_ne_none _, ?_⟩
        rw [step_right_cons]
        exact ih _ _ _ hr
  | cons a xs ih =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      refine ⟨Option.some_ne_none _, ?_⟩
      cases ys with
      | nil =>
        have hr : rest.length = max xs.length ([] : List Bool).length + 1 := by
          simp only [List.length_cons, List.length_nil, Nat.max_zero] at hlen ⊢
          omega
        rw [step_left_cons]
        simp only [List.headD_nil, List.tail_nil]
        exact ih _ _ _ _ hr
      | cons b ys =>
        have hr : rest.length = max xs.length ys.length + 1 := by
          simp only [List.length_cons] at hlen
          omega
        rw [step_left_cons]
        simp only [List.headD_cons, List.tail_cons]
        exact ih _ _ _ _ hr

theorem haltsAfter_sub (c : Bool) (xs ys zs bits : List Bool)
    (hlen : bits.length = max xs.length ys.length + 1) :
    HaltsAfter machine (cfg (some (borrowState c)) xs ys zs) bits := by
  refine ⟨activeFor_sub c xs ys zs bits hlen, ?_⟩
  rw [run_sub c xs ys zs bits hlen]
  rfl

def reverseMachine : BinaryMachine := FrameDecoder.machine.withEntry (2 : Fin 3)

def orientedMachine : BinaryMachine := Sequential.compose machine reverseMachine

theorem run_oriented (c : Bool) (xs ys first second : List Bool)
    (hfirst : first.length = max xs.length ys.length + 1)
    (hsecond : second.length = max xs.length ys.length + 1) :
    orientedMachine.run
      (liftLeft machine reverseMachine (cfg (some (borrowState c)) xs ys [])) (first ++ second) =
    liftRight machine reverseMachine (FrameDecoder.config none [] (subtractBits xs ys c) []) := by
  unfold orientedMachine
  rw [run_compose machine reverseMachine _ first second (haltsAfter_sub c xs ys [] first hfirst)]
  rw [run_sub c xs ys [] first hfirst]
  change liftRight machine reverseMachine
    ((FrameDecoder.machine.withEntry (2 : Fin 3)).run
      (FrameDecoder.config (some 2) [] [] ((subtractBits xs ys c).reverse ++ [])) second) = _
  erw [BinaryMachine.withEntry_run]
  have hlen : second.length = ((subtractBits xs ys c).reverse ++ []).length + 1 := by
    simpa only [List.append_nil, List.length_reverse, subtractBits_length] using hsecond
  rw [FrameDecoder.run_reverse [] [] _ second hlen]
  simp

theorem run_oriented_correct (xs ys first second : List Bool)
    (hsub : bitsValue ys ≤ bitsValue xs)
    (hfirst : first.length = max xs.length ys.length + 1)
    (hsecond : second.length = max xs.length ys.length + 1) :
    let result := orientedMachine.run
      (liftLeft machine reverseMachine (cfg (some 0) xs ys [])) (first ++ second)
    result.state = none ∧ result.«stacks» 0 = [] ∧ result.«stacks» 2 = [] ∧
      bitsValue (result.«stacks» 1) + bitsValue ys = bitsValue xs := by
  have h := run_oriented false xs ys first second hfirst hsecond
  change orientedMachine.run (liftLeft machine reverseMachine (cfg (some 0) xs ys []))
    (first ++ second) = _ at h
  dsimp only
  rw [h]
  have hs := subtractBits_correct xs ys false (by simpa using hsub)
  refine ⟨rfl, rfl, rfl, ?_⟩
  simpa [liftRight, FrameDecoder.config] using hs

theorem oriented_transition_bound (xs ys : List Bool) :
    2 * (max xs.length ys.length + 1) ≤ 2 * (xs.length + ys.length + 1) := by omega

end KS.W19.BinarySubtractor

end OAI
