import Mathlib
import OAI.Analysis.MatrixSigning.Machines.NormalizeOutput
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryAdder

namespace OAI

namespace KS.W01.BinaryAdder
open KS.W29
open KS.W19 (bitsValue digit)

theorem activeFor_of_length_le (c : Bool) (xs ys zs bits : List Bool)
    (hlen : bits.length ≤ max xs.length ys.length + 1) :
    Sequential.ActiveFor machine (cfg (some (carryState c)) xs ys zs) bits := by
  induction bits generalizing c xs ys zs with
  | nil => trivial
  | cons coin rest ih =>
      constructor
      · exact Option.some_ne_none _
      · cases xs with
        | nil =>
            cases ys with
            | nil =>
                have hr : rest = [] := by
                  apply List.length_eq_zero_iff.mp
                  simp only [List.length_cons, List.length_nil, max_self] at hlen
                  omega
                subst rest
                trivial
            | cons b ys =>
                rw [step_right_cons]
                apply ih
                simp only [List.length_nil, List.length_cons, Nat.zero_max] at hlen ⊢
                omega
        | cons a xs =>
            rw [step_left_cons]
            apply ih
            cases ys with
            | nil =>
                simp only [List.tail_nil, List.length_nil, List.length_cons, Nat.max_zero]
                  at hlen ⊢
                omega
            | cons b ys =>
                simp only [List.tail_cons, List.length_cons] at hlen ⊢
                omega

theorem haltsAfter (c : Bool) (xs ys zs bits : List Bool)
    (hlen : bits.length = max xs.length ys.length + 1) :
    Sequential.HaltsAfter machine (cfg (some (carryState c)) xs ys zs) bits := by
  constructor
  · exact activeFor_of_length_le c xs ys zs bits hlen.le
  · rw [run_add c xs ys zs bits hlen]
    rfl

def normalizedMachine : BinaryMachine := Sequential.compose machine NormalizeOutput.machine

theorem run_normalized (xs ys first second : List Bool)
    (hfirst : first.length = max xs.length ys.length + 1)
    (hsecond : second.length = (addBits false xs ys).length + 1) :
    normalizedMachine.run
      (Sequential.liftLeft machine NormalizeOutput.machine (cfg (some 0) xs ys []))
      (first ++ second) =
      Sequential.liftRight machine NormalizeOutput.machine
        (FrameDecoder.config none [] (addBits false xs ys) []) := by
  apply NormalizeOutput.compose_result
  · exact haltsAfter false xs ys [] first hfirst
  · have h := run_add false xs ys [] first hfirst
    change machine.run (cfg (some 0) xs ys []) first = _ at h
    rw [h]
    simp only [List.append_nil]
    rfl
  · exact hsecond

theorem normalized_transition_bound (xs ys : List Bool) :
    (max xs.length ys.length + 1) + ((addBits false xs ys).length + 1) ≤
      2 * (xs.length + ys.length) + 3 := by
  have h := addBits_length_le false xs ys
  omega

theorem normalized_output_correct (xs ys first second : List Bool)
    (hfirst : first.length = max xs.length ys.length + 1)
    (hsecond : second.length = (addBits false xs ys).length + 1) :
    let final := normalizedMachine.run
      (Sequential.liftLeft machine NormalizeOutput.machine (cfg (some 0) xs ys []))
      (first ++ second)
    final.state = none ∧ final.«stacks» 0 = [] ∧ final.«stacks» 2 = [] ∧
      bitsValue (final.«stacks» 1) = bitsValue xs + bitsValue ys := by
  dsimp only
  rw [run_normalized xs ys first second hfirst hsecond]
  simp [Sequential.liftRight, FrameDecoder.config, addBits_correct, digit]
  rfl

end KS.W01.BinaryAdder

end OAI
