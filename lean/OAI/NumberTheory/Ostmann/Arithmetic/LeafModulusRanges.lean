import OAI.NumberTheory.Ostmann.Construction.HistorySmoothBound

namespace OAI

/-! # The leaf modulus from the giant, protected and compensation ranges -/

namespace Ostmann

/-- `P`, `U`, and `D` are the products of protected, compensation, and
outside spectator slots. The center identity is equation (45). -/
theorem leaf_modulus_lower_from_ranges
    (X x₁ x₂ P U D G tD J W Δ cG cP cU cD : ℝ)
    (hX : 0 < X) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hP : 0 < P) (hU : 0 < U) (hD : 0 < D)
    (hcenter : 2 * G + 2 * tD + J + W = Real.log X + Δ)
    (hg₁ : G - cG ≤ Real.log x₁) (hg₂ : G - cG ≤ Real.log x₂)
    (hp : J - cP ≤ Real.log P) (hu : W - cU ≤ Real.log U)
    (hd : 2 * tD - cD ≤ Real.log D) :
    X * Real.exp (Δ - (2 * cG + cP + cU + cD)) ≤ x₁ * x₂ * P * U * D := by
  have hM : 0 < x₁ * x₂ * P * U * D := by positivity
  have hlog : Real.log (x₁ * x₂ * P * U * D) =
      Real.log x₁ + Real.log x₂ + Real.log P + Real.log U + Real.log D := by
    rw [Real.log_mul (by positivity) (ne_of_gt hD),
      Real.log_mul (by positivity) (ne_of_gt hU),
      Real.log_mul (by positivity) (ne_of_gt hP),
      Real.log_mul (ne_of_gt hx₁) (ne_of_gt hx₂)]
  have hlow : Real.log X + (Δ - (2 * cG + cP + cU + cD)) ≤
      Real.log (x₁ * x₂ * P * U * D) := by rw [hlog]; linarith
  calc
    _ = Real.exp (Real.log X + (Δ - (2 * cG + cP + cU + cD))) := by
      rw [Real.exp_add, Real.exp_log hX]
    _ ≤ Real.exp (Real.log (x₁ * x₂ * P * U * D)) := Real.exp_le_exp.mpr hlow
    _ = _ := Real.exp_log hM

/-- The corresponding size of the square-root prefactor in a leaf of
equation (50); the error in the exponent is independent of frequency. -/
theorem leaf_sqrt_ratio_from_ranges
    (X x₁ x₂ P U D G tD J W Δ cG cP cU cD : ℝ)
    (hX : 0 < X) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hP : 0 < P) (hU : 0 < U) (hD : 0 < D)
    (hcenter : 2 * G + 2 * tD + J + W = Real.log X + Δ)
    (hg₁ : G - cG ≤ Real.log x₁) (hg₂ : G - cG ≤ Real.log x₂)
    (hp : J - cP ≤ Real.log P) (hu : W - cU ≤ Real.log U)
    (hd : 2 * tD - cD ≤ Real.log D) :
    Real.sqrt (X / (x₁ * x₂ * P * U * D)) ≤
      Real.exp (((2 * cG + cP + cU + cD) - Δ) / 2) :=
  sqrt_ratio_le_exp X _ Δ _ (by positivity)
    (leaf_modulus_lower_from_ranges X x₁ x₂ P U D G tD J W Δ cG cP cU cD
      hX hx₁ hx₂ hP hU hD hcenter hg₁ hg₂ hp hu hd)

end Ostmann

end OAI
