import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEulerPhysical

namespace OAI

/-! Falling Euler derivatives on a tail only require smoothness on that tail. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
local notation "V" => ℂ × ℂ

theorem homogeneousPair_iteratedDeriv_smooth_tail (U : ℝ → V) (R : ℝ)
    (hU : ContDiffOn ℝ ∞ U (Ioi R)) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv n U) (Ioi R) := by
  induction n with
  | zero => simpa using hU
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

theorem homogeneousEulerDeriv_physical_tail (U : ℝ → V) (L : ℝ)
    (hU : ContDiffOn ℝ ∞ U (Ioi (Real.exp L))) (n : ℕ) (t : ℝ) (ht : L<t) :
    homogeneousEulerDeriv (fun s => U (Real.exp s)) n t =
      Real.exp ((n : ℝ)*t) • iteratedDeriv n U (Real.exp t) := by
  induction n generalizing t with
  | zero => simp [homogeneousEulerDeriv]
  | succ n ih =>
      have heq : homogeneousEulerDeriv (fun s => U (Real.exp s)) n =ᶠ[𝓝 t]
          (fun s => Real.exp ((n : ℝ)*s) • iteratedDeriv n U (Real.exp s)) := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact ih s hs
      have het : Real.exp L < Real.exp t := Real.exp_lt_exp.mpr ht
      have hUn : HasDerivAt (iteratedDeriv n U) (iteratedDeriv (n+1) U (Real.exp t))
          (Real.exp t) := by
        rw [iteratedDeriv_succ]
        exact (((homogeneousPair_iteratedDeriv_smooth_tail U (Real.exp L) hU n) _ het).contDiffAt
          (Ioi_mem_nhds het)).differentiableAt (by simp) |>.hasDerivAt
      have hUt : HasDerivAt (fun s => iteratedDeriv n U (Real.exp s))
          (Real.exp t • iteratedDeriv (n+1) U (Real.exp t)) t :=
        hUn.scomp t (Real.hasDerivAt_exp t)
      have hweight : HasDerivAt (fun s : ℝ => Real.exp ((n : ℝ)*s))
          ((n : ℝ)*Real.exp ((n : ℝ)*t)) t := by
        convert ((hasDerivAt_id t).const_mul (n : ℝ)).exp using 1 <;> simp [mul_comm]
      have hh := hweight.smul hUt
      have hd := hh.congr_of_eventuallyEq heq
      change deriv (homogeneousEulerDeriv (fun s => U (Real.exp s)) n) t -
        (n : ℝ) • homogeneousEulerDeriv (fun s => U (Real.exp s)) n t = _
      rw [hd.deriv,ih t ht]
      simp only [smul_smul]
      have hexp : Real.exp ((n : ℝ)*t)*Real.exp t=Real.exp (((n+1 : ℕ) : ℝ)*t) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp]
      abel

end DefocusingNLS

end OAI
