import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEulerRecurrence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! # Falling Euler derivatives are the actual radial derivatives

This identity converts the exact logarithmic coefficient recurrence back to
the top physical derivative occurring in the homogeneous Sobolev norm.
-/

open Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

local notation "V" => ℂ × ℂ

theorem homogeneousPair_iteratedDeriv_smooth (U : ℝ → V)
    (hU : ContDiffOn ℝ ∞ U (Ioi 0)) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv n U) (Ioi 0) := by
  induction n with
  | zero => simpa using hU
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

theorem homogeneousEulerDeriv_physical (U : ℝ → V)
    (hU : ContDiffOn ℝ ∞ U (Ioi 0)) (n : ℕ) (t : ℝ) :
    homogeneousEulerDeriv (fun s => U (Real.exp s)) n t =
      Real.exp ((n : ℝ) * t) • iteratedDeriv n U (Real.exp t) := by
  induction n generalizing t with
  | zero => simp [homogeneousEulerDeriv]
  | succ n ih =>
      have heq : homogeneousEulerDeriv (fun s => U (Real.exp s)) n =
          (fun s => Real.exp ((n : ℝ) * s) • iteratedDeriv n U (Real.exp s)) := funext ih
      have hUn : HasDerivAt (iteratedDeriv n U) (iteratedDeriv (n + 1) U (Real.exp t))
          (Real.exp t) := by
        rw [iteratedDeriv_succ]
        exact (((homogeneousPair_iteratedDeriv_smooth U hU n) _ (Real.exp_pos t)).contDiffAt
          (Ioi_mem_nhds (Real.exp_pos t))).differentiableAt (by simp) |>.hasDerivAt
      have hUt : HasDerivAt (fun s => iteratedDeriv n U (Real.exp s))
          (Real.exp t • iteratedDeriv (n + 1) U (Real.exp t)) t :=
        hUn.scomp t (Real.hasDerivAt_exp t)
      have hweight : HasDerivAt (fun s : ℝ => Real.exp ((n : ℝ) * s))
          ((n : ℝ) * Real.exp ((n : ℝ) * t)) t := by
        convert ((hasDerivAt_id t).const_mul (n : ℝ)).exp using 1 <;> simp [mul_comm]
      have hh := hweight.smul hUt
      change HasDerivAt (fun s => Real.exp ((n : ℝ) * s) • iteratedDeriv n U (Real.exp s)) _ t at hh
      change deriv (homogeneousEulerDeriv (fun s => U (Real.exp s)) n) t -
        (n : ℝ) • homogeneousEulerDeriv (fun s => U (Real.exp s)) n t = _
      rw [heq, hh.deriv]
      simp only [smul_smul]
      have hexp : Real.exp ((n : ℝ) * t) * Real.exp t = Real.exp (((n + 1 : ℕ) : ℝ) * t) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp]
      abel

end DefocusingNLS

end OAI
