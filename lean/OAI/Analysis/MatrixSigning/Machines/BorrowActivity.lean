import Mathlib
import OAI.Analysis.MatrixSigning.Machines.Sequential
import OAI.Analysis.MatrixSigning.Arithmetic.BorrowSubtractor

namespace OAI

namespace KS.W19.BorrowSubtractor
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

end KS.W19.BorrowSubtractor

end OAI
