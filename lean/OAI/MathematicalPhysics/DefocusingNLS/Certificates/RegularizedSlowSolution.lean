import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! # The regularized integral defining the outgoing slow solution

The integral in Lemma `free:slow`, specialized to integer `m`, subtracts a
constant from the bracket to remove one order of the endpoint singularity.
-/

open MeasureTheory Filter Topology

namespace DefocusingNLS

noncomputable section

def regularizingBracket (r x u : ℂ) : ℂ := (1 + u / x) ^ r - 1

theorem hasDerivAt_regularizingBracket (r x : ℂ) :
    HasDerivAt (regularizingBracket r x) (r / x) 0 := by
  change HasDerivAt (fun u : ℂ => (1 + u / x) ^ r - 1) (r / x) 0
  have h : HasDerivAt (fun u : ℂ => 1 + u / x) (1 / x) 0 :=
    ((hasDerivAt_id 0).div_const x).const_add 1
  simpa only [zero_div, zero_mul, add_zero, Complex.one_cpow, one_mul, mul_one,
    div_eq_mul_inv] using
    (h.cpow_const (c := r)
      (by simp : (1 + (0 : ℂ) / x) ∈ Complex.slitPlane)).sub_const 1

/-- The precise endpoint cancellation needed before proving integrability. -/
theorem regularizingBracket_isBigO (r x : ℂ) :
    regularizingBracket r x =O[𝓝 0] (fun u : ℂ => u) := by
  change (fun u : ℂ => (1 + u / x) ^ r - 1) =O[𝓝 0] (fun u : ℂ => u)
  simpa only [regularizingBracket, zero_div, add_zero, Complex.one_cpow,
    sub_self, sub_zero] using (hasDerivAt_regularizingBracket r x).isBigO_sub

/-- The manuscript's regularized Laplace representation. -/
def regularizedSlowKernel (q : ℂ) (m : ℕ) (x : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-(u : ℂ)) * (u : ℂ) ^ (q - 1) *
    regularizingBracket ((m : ℂ) - 1 - q) x u

def regularizedSlowSolution (q : ℂ) (m : ℕ) (x : ℂ) : ℂ :=
  x ^ (-q) * (1 + (Complex.Gamma q)⁻¹ *
    ∫ u : ℝ in Set.Ioi 0, regularizedSlowKernel q m x u)

theorem regularizedSlowSolution_zero (m : ℕ) (x : ℂ) :
    regularizedSlowSolution 0 m x = 1 := by
  simp [regularizedSlowSolution, Complex.Gamma_zero]

theorem hasDerivAt_regularizedSlowSolution_zero (m : ℕ) (x : ℂ) :
    HasDerivAt (regularizedSlowSolution 0 m) 0 x := by
  have h : regularizedSlowSolution 0 m = (fun _ : ℂ => 1) :=
    funext (regularizedSlowSolution_zero m)
  rw [h]
  exact hasDerivAt_const x (1 : ℂ)

end
end DefocusingNLS

end OAI
