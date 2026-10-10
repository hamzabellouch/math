import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FixedCutoffProfileDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingNearbyTransfer

namespace OAI

/-! # Uniform cutoff-profile estimates in a nearby fixed radius -/

open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

attribute [local irreducible] fixedCutoffProfile expandingNearbyTransfer

theorem fixedCutoffProfile_eq_transfer (a k : ℝ) (ha : 0 < a)
    (ha1 : a < 1) (hk : 8 < k) (M R : Radius)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    fixedCutoffProfile a k ha ha1 hk M χ hχ Q hQ R.1 =
      expandingNearbyTransfer a k ha hk R M
        (schwartzTorusSample a k R.1 ha1 hk R.2
          (radianFourierKernel (cutoffProfileSchwartz R.1
            (lt_of_lt_of_le zero_lt_one R.2) χ hχ Q hQ))) := by
  ext n
  rw [fixedCutoffProfile_coordinate, expandingNearbyTransfer_apply]
  change (expandingSobolevWeight a k M.1 n : ℂ) * _ =
    ((expandingSobolevWeight a k M.1 n / expandingSobolevWeight a k R.1 n : ℝ) : ℂ) *
      ((expandingSobolevWeight a k R.1 n : ℂ) *
        schwartzLatticeCoefficient R.1
          (radianFourierKernel (cutoffProfileSchwartz R.1 _ χ hχ Q hQ)) n)
  rw [cutoffProfile_coefficient_fixed_scale, Complex.ofReal_div, ← mul_assoc,
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k R.1 R.2 n).ne')]

theorem fixedCutoffProfile_norm_le (a k : ℝ) (ha : 0 < a)
    (ha1 : a < 1) (hk : 8 < k) (M R : Radius)
    (hMR : M.1 ≤ 2 * R.1) (hRM : R.1 ≤ 2 * M.1)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (B : ℝ)
    (hB : ‖schwartzTorusSample a k R.1 ha1 hk R.2
      (radianFourierKernel (cutoffProfileSchwartz R.1
        (lt_of_lt_of_le zero_lt_one R.2) χ hχ Q hQ))‖ ≤ B) :
    ‖fixedCutoffProfile a k ha ha1 hk M χ hχ Q hQ R.1‖ ≤
      (2 ^ a + 2 ^ (k - 6)) * B := by
  rw [fixedCutoffProfile_eq_transfer]
  exact ((expandingNearbyTransfer a k ha hk R M).le_opNorm _).trans
    (mul_le_mul (expandingNearbyTransfer_norm_le a k ha hk R M hMR hRM)
      hB (norm_nonneg _) (by positivity))

end DefocusingNLS

end OAI
