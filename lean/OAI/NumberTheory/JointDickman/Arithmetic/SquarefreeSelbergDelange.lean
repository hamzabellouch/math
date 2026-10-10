import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeUnsmoothing
import OAI.NumberTheory.JointDickman.Analysis.RieszLogTail
import OAI.NumberTheory.JointDickman.Amplification.LogErrorAllCutoffs

namespace OAI

/-! # Discharge of the squarefree Selberg--Delange input

The actual squarefree coefficients are handled by Perron inversion,
the proved zeta zero-free region, and positive finite-difference unsmoothing.
Only the two exponents used by the main theorem are packaged as an input.
-/
namespace JointDickman
open Filter Asymptotics Finset
open scoped Topology

theorem squarefreeSummatory_expansion {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∀ H : ℕ, (fun x : ℝ => squarefreeSummatory z x-
        x*∑ j ∈ range (H+1), c j*(Real.log x)^(z-1-j)) =O[atTop]
          (fun x => x*(Real.log x)^(z-2-H)) := by
  obtain ⟨b,hb,hb0,h⟩ := squarefreeSummatory_derivative_approx hz hz1
  refine ⟨rieszUnsmoothCoefficients b z,?_,?_,fun H => ?_⟩
  · simp only [rieszUnsmoothCoefficients,hb]
    ring
  · change 0 < 2*b 0
    positivity
  · have hh := (h H).add (rieszLogDerivative_truncation b z H (2*H+2) (by omega))
    apply hh.congr_left
    intro x
    ring

theorem squarefreeSelbergDelangeInput : PublishedInputs.SquarefreeSelbergDelangeInput := by
  intro z hz
  have hz0 : 0 < z := by rcases hz with rfl | rfl <;> norm_num
  have hz1 : z < 1 := by rcases hz with rfl | rfl <;> norm_num
  obtain ⟨c,hc,hc0,h⟩ := squarefreeSummatory_expansion hz0 hz1
  refine ⟨c,hc,hc0,fun H => ?_⟩
  apply log_error_all_cutoffs
    (fun x hx => squarefreeSummatory_abs_le hz0.le hz1.le (by linarith : 0 ≤ x))
    _ (h H)
  intro x hx
  exact (HasDerivAt.fun_sum (u := range (H+1)) (fun (j : ℕ) _ =>
    (hasDerivAt_log_rpow (z-1-j) (by linarith : 1 < x)).const_mul (c j))).continuousAt

end JointDickman

end OAI
