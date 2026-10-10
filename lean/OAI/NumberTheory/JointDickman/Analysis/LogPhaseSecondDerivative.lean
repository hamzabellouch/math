import OAI.NumberTheory.JointDickman.Analysis.LogPhaseDerivatives
import OAI.NumberTheory.JointDickman.Amplification.SecondDerivativeTest

namespace OAI

/-! # The second-derivative bound after logarithmic differencing -/
namespace JointDickman
open Set Problem337
open scoped ContDiff

/-- All derivative information is proved for the actual logarithmic phase.
The interval includes the full displacement introduced by differencing. -/
theorem logarithmic_difference_sum_bound (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (a Z U x : ℝ) (N : ℕ)
    (hZ : Z ≠ 0) (hU : 0 < U) (hx : U ≤ x)
    (hend : x+(N:ℝ)+hs.sum ≤ 4*U) :
    let lam : ℝ := hs.prod*((hs.length+1).factorial:ℝ)*|Z|/(4*U)^(hs.length+2)
    ‖∑ j ∈ Finset.range N, ExponentialSum.phase
      (forwardDifference hs (fun y => a*y+Z*Real.log y) ((j:ℝ)+x))‖ ≤
      (6*(4:ℝ)^(hs.length+2)+15)*((N:ℝ)*Real.sqrt lam+1/Real.sqrt lam) := by
  let g : ℝ → ℝ := forwardDifference hs (fun y => a*y+Z*Real.log y)
  let lam : ℝ := hs.prod*((hs.length+1).factorial:ℝ)*|Z|/(4*U)^(hs.length+2)
  have hlam : 0 < lam := by
    dsimp [lam]
    exact div_pos (mul_pos (mul_pos (List.prod_pos hhs)
      (by exact_mod_cast Nat.factorial_pos _)) (abs_pos.mpr hZ)) (by positivity)
  have hg : ContDiffOn ℝ ∞ g (Ioi 0) :=
    forwardDifference_contDiffOn hs (fun h hh => (hhs h hh).le)
      (logarithmic_linear_phase_smooth a Z)
  have hg' : ContDiffOn ℝ ∞ (deriv g) (Ioi 0) :=
    hg.deriv_of_isOpen isOpen_Ioi (by simp)
  have hy0 (y : ℝ) (hy : y ∈ Icc x (x+N)) : 0 < y := hU.trans_le (hx.trans hy.1)
  have hf (y : ℝ) (hy : y ∈ Icc x (x+N)) : HasDerivAt g (deriv g y) y :=
    ((hg.contDiffAt (isOpen_Ioi.mem_nhds (hy0 y hy))).differentiableAt (by simp)).hasDerivAt
  have hf' (y : ℝ) (hy : y ∈ Icc x (x+N)) :
      HasDerivAt (deriv g) (iteratedDeriv 2 g y) y := by
    simpa only [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_zero] using
      ((hg'.contDiffAt (isOpen_Ioi.mem_nhds (hy0 y hy))).differentiableAt (by simp)).hasDerivAt
  have hb (y : ℝ) (hy : y ∈ Icc x (x+N)) :
      lam ≤ |iteratedDeriv 2 g y| ∧
      |iteratedDeriv 2 g y| ≤ (4:ℝ)^(hs.length+2)*lam := by
    have hh := logarithmic_linear_forwardDifference_second_bounds hs hhs a Z (V := 4*U) hU
      (hx.trans hy.1) (by linarith [hy.2])
    refine ⟨hh.1,hh.2.trans_eq ?_⟩
    dsimp [lam]
    rw [mul_pow]
    field_simp
  exact ExponentialSum.second_derivative_test g (deriv g) (iteratedDeriv 2 g)
    x N lam ((4:ℝ)^(hs.length+2)) hlam (by positivity) hf hf' hb

end JointDickman

end OAI
