import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

namespace OAI

/-! # The odd-power defocusing nonlinearity

For an odd power `p = 2m + 1`, the scalar nonlinearity is a real polynomial
in a complex variable and its conjugate. Its real derivative has the two
circular components used in the linearized equation.
-/

namespace DefocusingNLS

noncomputable section

def oddPowerNonlinearity (m : ℕ) (z : ℂ) : ℂ := z ^ (m + 1) * star z ^ m

theorem oddPowerNonlinearity_eq (m : ℕ) (z : ℂ) :
    oddPowerNonlinearity m z = ((‖z‖ ^ (2 * m) : ℝ) : ℂ) * z := by
  calc
    oddPowerNonlinearity m z = (z * star z) ^ m * z := by
      rw [oddPowerNonlinearity, mul_pow, pow_succ]
      ring
    _ = ((‖z‖ ^ (2 * m) : ℝ) : ℂ) * z := by
      have hz : z * star z = (Complex.normSq z : ℂ) := by
        simpa only [starRingEnd_apply] using Complex.mul_conj z
      rw [hz, ← Complex.sq_norm, ← Complex.ofReal_pow, ← pow_mul]

def oddPowerDerivative (m : ℕ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (((m + 1 : ℕ) : ℂ) * z ^ m * star z ^ m) • ContinuousLinearMap.id ℝ ℂ +
    ((m : ℂ) * z ^ (m + 1) * star z ^ (m - 1)) •
      (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap

theorem hasFDerivAt_oddPowerNonlinearity (m : ℕ) (z : ℂ) :
    HasFDerivAt (oddPowerNonlinearity m) (oddPowerDerivative m z) z := by
  have h := ((hasFDerivAt_id z (𝕜 := ℝ)).pow (m + 1)).mul
    (((hasFDerivAt_id z (𝕜 := ℝ)).star).pow m)
  apply h.congr_fderiv
  ext v : 1
  simp [oddPowerDerivative, nsmul_eq_mul, smul_eq_mul]
  ring

theorem contDiff_oddPowerNonlinearity (m : ℕ) :
    ContDiff ℝ ⊤ (oddPowerNonlinearity m) := by
  exact (contDiff_id.pow (m + 1)).mul
    ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.pow m)

end
end DefocusingNLS

end OAI
