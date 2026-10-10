import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalParameter
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalSource
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalParameterEquation

namespace OAI

/-! The physical outgoing parameter derivative has precisely the Jordan
source, including the logarithmic derivative of the radial power. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralPhysicalShear_hasDerivAt (μ lam η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ → ℂ) (Y D : ℝ → E₄) (r : ℝ) (hr : 0 < r)
    (hscale : (Complex.exp (μ * (Real.log r : ℂ)) *
      star (Complex.exp (μ * (Real.log r : ℂ)))) ^ m = 1 / (r : ℂ) ^ 2)
    (hY : HasDerivAt Y (circularLeadingField (Real.log r) (Y (Real.log r)) +
      circularBoundedField (μ - 2 * lam) (star μ - 2 * lam) η m (q (Real.log r))
        (Y (Real.log r))) (Real.log r))
    (hD : HasDerivAt D (circularLeadingField (Real.log r) (D (Real.log r)) +
      circularBoundedField (μ - 2 * lam) (star μ - 2 * lam) η m (q (Real.log r))
        (D (Real.log r)) + circularPointSlopeCLM μ (star μ) lam (Y (Real.log r))) (Real.log r)) :
    let Z := fun t => circularParameterShear t (Y t) (D t)
    let V := spectralPhysicalPair (μ - 2 * lam) (star μ - 2 * lam) Y r
    HasDerivAt (spectralPhysicalPair (μ - 2 * lam) (star μ - 2 * lam) Z)
      (spectralPhysicalCircularField (μ - 2 * lam) (star μ - 2 * lam) η m
        (Complex.exp (μ * (Real.log r : ℂ)) * q (Real.log r)) r
        (spectralPhysicalPair (μ - 2 * lam) (star μ - 2 * lam) Z r) +
        ((0, -Complex.I * V.1.1), (0, Complex.I * V.2.1))) r := by
  have hs : circularPointSlopeCLM (μ - 2 * lam) (star μ - 2 * lam) 0 (Y (Real.log r)) =
      circularPointSlopeCLM μ (star μ) lam (Y (Real.log r)) := by
    change ((0, 4 * (Y (Real.log r)).1.2 +
        (4 * ((μ - 2 * lam) - 2 * 0) + 20) * (Y (Real.log r)).1.1),
      (0, 4 * (Y (Real.log r)).2.2 +
        (4 * ((star μ - 2 * lam) - 2 * 0) + 20) * (Y (Real.log r)).2.1)) = _
    simp only [mul_zero, sub_zero]
    rfl
  have hd := circularParameterShear_hasDerivAt (μ - 2 * lam) (star μ - 2 * lam) η m
    (q (Real.log r)) Y D (Real.log r) hY (by simpa only [hs] using hD)
  have hp := spectralPhysicalPair_source_hasDerivAt μ lam η m hm q _ r hr
    (-Complex.I * (Real.exp (2 * Real.log r) : ℂ) * (Y (Real.log r)).1.1)
    (Complex.I * (Real.exp (2 * Real.log r) : ℂ) * (Y (Real.log r)).2.1) hscale hd
  apply hp.congr_deriv
  have he : Real.exp (2 * Real.log r) = r ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log hr]
    ring
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  congr 1
  apply Prod.ext <;> apply Prod.ext
  · rfl
  · dsimp only [spectralPhysicalPair, spectralPhysicalJet]
    rw [he]
    push_cast
    field_simp
  · rfl
  · dsimp only [spectralPhysicalPair, spectralPhysicalJet]
    rw [he]
    push_cast
    field_simp

end DefocusingNLS

end OAI
