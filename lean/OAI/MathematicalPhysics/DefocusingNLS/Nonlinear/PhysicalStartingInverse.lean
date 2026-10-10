import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalReferenceModulation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevSymmetryFlow

namespace OAI

/-! # Undoing the physical starting-coordinate map -/

namespace DefocusingNLS
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem expandingPhysicalInitial_physicalStarting (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : Radius) (θ : ℝ) (x : SchrodingerTorus) (f : FourierL2) :
    expandingPhysicalInitialEquiv a k L.1 ha ha1 hk L.2
        (physicalStartingOperator a k ha hk L θ x f) =
      Complex.exp ((-θ : ℝ) * Complex.I) • sobolevTranslation x f := by
  have hInv (v : FourierL2) : expandingInverseTransfer a k L.1 ha hk L.2
      (expandingScaleTransfer a k 1 L.1 ha hk le_rfl L.2 v) = v :=
    congrArg (fun A : FourierL2 →L[ℂ] FourierL2 => A v)
      (expandingWeightUnit a k L.1 ha hk L.2).inv_val
  have hAmp : physicalStartingAmplitude a L θ * (L.1 ^ (2 * a) : ℝ) =
      Complex.exp ((-θ : ℝ) * Complex.I) := by
    have h := physicalStartingAmplitude_expandingRadius a L L 0 θ (by simp [expandingRadius])
    simpa using h
  rw [expandingPhysicalInitialEquiv_apply]
  change ((L.1 ^ (2 * a) : ℝ) : ℂ) • expandingToSobolev a k ha1 hk
      (expandingInverseTransfer a k L.1 ha hk L.2
        (physicalStartingAmplitude a L θ • expandingScaleTransfer a k 1 L.1 ha hk le_rfl L.2
          (sobolevToExpanding a k ha hk (sobolevTranslation x f)))) = _
  rw [map_smul, map_smul, hInv, expandingToSobolev_sobolevToExpanding, smul_smul,
    mul_comm ((L.1 ^ (2 * a) : ℝ) : ℂ), hAmp]

theorem maximalSobolev_phase_translation_norm (k : ℝ) (hk : 6 < k) (m : ℕ)
    (c : Circle) (x : SchrodingerTorus) (f : FourierL2) (t : ℝ)
    (ht : t ∈ maximalSobolevInteractionDomain k hk m f) :
    ‖sobolevTorusFunction k (maximalSobolevSchrodingerFlow k hk m
        (sobolevPhase c (sobolevTranslation x f)) t) 0‖ =
      ‖sobolevTorusFunction k (maximalSobolevSchrodingerFlow k hk m f t) x‖ := by
  rw [maximalSobolevSchrodingerFlow_phase k hk m c (sobolevTranslation x f) t
    (by rwa [maximalSobolevInteractionDomain_translation]),
    maximalSobolevSchrodingerFlow_translation k hk m x f t ht,
    sobolevTorusFunction_phase k hk, sobolevTorusFunction_translation k hk, add_zero, norm_mul]
  simp

end DefocusingNLS

end OAI
