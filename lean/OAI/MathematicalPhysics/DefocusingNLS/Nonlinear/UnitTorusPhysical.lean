import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.UnitTorusCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSmoothFilter

namespace OAI

/-! # The exact physical scaling of continuous functions on the unit torus -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingUnitTorusFunction_physical (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) (y : E) :
    expandingUnitTorusFunction a k L f (unitTorusProjection ((2 * Real.pi * L)⁻¹ • y)) =
      expandingPhysicalContinuous a k L ha ha1 hk hL f y := by
  rw [expandingUnitTorusFunction_projection a k L ha ha1 hk hL,
    expandingPhysicalContinuous_apply]
  congr 2
  rw [smul_smul]
  congr 1
  field_simp

theorem expandingUnitTorusFunction_sample (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (K : 𝓢(E, ℂ)) :
    expandingUnitTorusFunction a k L
      (schwartzTorusSample a k L ha1 hk hL (radianFourierKernel K)) =
        schwartzPeriodizedTorus (periodizationRescale L (by linarith) K) := by
  ext x
  obtain ⟨y, rfl⟩ := unitTorusProjection_isOpenQuotientMap.surjective x
  rw [expandingUnitTorusFunction_projection a k L ha ha1 hk hL,
    schwartzPeriodizedTorus_projection, schwartzPeriodization_apply]
  have hy : (2 * Real.pi) • y = L⁻¹ • ((2 * Real.pi * L) • y) := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [hy, schwartzTorusSample_physical a k L ha ha1 hk hL]
  apply tsum_congr
  intro n
  rw [periodizationRescale_apply, smul_add]

end DefocusingNLS

end OAI
