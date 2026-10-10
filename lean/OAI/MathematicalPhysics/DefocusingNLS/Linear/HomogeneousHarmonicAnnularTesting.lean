import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialSquareTest

namespace OAI

/-! # Arbitrary annular tests for the projected Laplacian -/

open Set MeasureTheory
open scoped ContDiff SchwartzMap Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem harmonicAngularCoefficient_annular_laplacian
    (Y F : E → ℂ) (lam : ℂ)
    (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x)
    (hRay : ∀ (x : E) (t : ℝ), 0 < t → Y (t • x) = Y x)
    (hEigen : ∀ x : E, x ≠ 0 → Δ Y x = -(lam / (‖x‖ ^ 2 : ℝ)) * Y x)
    (hF : ContDiff ℝ 2 F)
    (φ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi (0 : ℝ)) :
    (∫ r : PhysicalPositiveRadius, φ r * harmonicAngularCoefficient Y (Δ F) r
      ∂physicalRadiusMeasure) =
    ∫ r : PhysicalPositiveRadius,
      (deriv (deriv φ) r + ((11 / r.1 : ℝ) : ℂ) * deriv φ r -
        lam / (r.1 ^ 2 : ℝ) * φ r) * harmonicAngularCoefficient Y F r
      ∂physicalRadiusMeasure := by
  let ψ := radialSquareSchwartz φ hc hs
  have hψc : HasCompactSupport ψ := radialSquarePullback_hasCompactSupport φ hc hs
  have hψs : tsupport ψ ⊆ Ioi (0 : ℝ) := tsupport_radialSquarePullback φ hs
  have h := harmonicAngularCoefficient_weak_laplacian Y F lam hY hRay hEigen hF
    ψ hψc hψs
  calc
    _ = ∫ r : PhysicalPositiveRadius, ψ (r.1 ^ 2) *
        harmonicAngularCoefficient Y (Δ F) r ∂physicalRadiusMeasure := by
      apply integral_congr_ae
      filter_upwards [] with r
      rw [radialSquareSchwartz_square φ hc hs r.1 r.2]
    _ = _ := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with r
      rw [radialSquareSchwartz_laplacian_test φ hc hs lam r.1 r.2]

end DefocusingNLS

end OAI
