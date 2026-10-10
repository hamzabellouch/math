import OAI.Geometry.SurfaceImmersion.Geometry.ExplicitPowerThreshold

namespace OAI

/-! Polynomial reciprocal control for explicit positive-power thresholds.
No compactness choice enters the numerical threshold. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection
open RealModes

theorem powerThreshold_inverse_polynomial (n : ℕ) (c b C B : ℝ → ℝ)
    (hC : HasPolynomialBound C) (hB : HasPolynomialBound B)
    (hc : ∀ x, 1 ≤ x → 0 ≤ c x) (hb : ∀ x, 1 ≤ x → 0 < b x)
    (hcC : ∀ x, 1 ≤ x → c x ≤ C x)
    (hbB : ∀ x, 1 ≤ x → (b x)⁻¹ ≤ B x) :
    HasPolynomialBound (fun x => (powerThreshold n (c x) (b x))⁻¹) := by
  apply HasPolynomialBound.of_le
    (((polynomialBound_const zero_le_one).add
      ((hC.add (polynomialBound_const zero_le_one)).mul hB)).pow n)
  · intro x hx
    apply inv_nonneg.mpr
    unfold powerThreshold
    exact pow_nonneg (le_min zero_le_one (div_nonneg (hb x hx).le (by linarith [hc x hx]))) _
  · intro x hx
    exact powerThreshold_inverse_le (hc x hx) (hb x hx) (hcC x hx) (hbB x hx)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
