import OAI.Geometry.RCD.Harmonic.TwoCenterDirectionEstimate

namespace OAI

/-! # Uniform physical scaling of the constant-direction estimate -/

namespace RegularPointCoordinates

noncomputable def directionRecoveryError (A V E C : ℝ) : ℝ :=
  2 * A * Real.sqrt E + Real.sqrt C + A * Real.sqrt (2 * E) + Real.sqrt (2 * V) / 4

noncomputable def directionRecoveryConstant (A V E C G M : ℝ) : ℝ :=
  Real.sqrt (2 * V) + (81920 * G + 4 * M) * directionRecoveryError A V E C

/-- The error obtained from the actual radial fits has one length factor
and one square root of the original pair source envelope. -/
theorem direction_recovery_scaled_error {s A V E C x z p : ℝ}
    (hs : 0 < s) (hA : 0 ≤ A) (hV : 0 ≤ V) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hx : 0 ≤ x) (hz : 0 ≤ z) (_hp : 0 ≤ p) (hpS : p ≤ x + z) :
    (2 * A * s) * Real.sqrt (E * z) + Real.sqrt (C * s ^ 2 * p) +
      (A * s) * Real.sqrt (2 * (E * z) + 2 * (E * x)) +
      Real.sqrt (2 * (V * s ^ 2 * z) + 2 * (V * s ^ 2 * x)) / 4 ≤
      s * directionRecoveryError A V E C * Real.sqrt (x + z) := by
  have hS : 0 ≤ x + z := add_nonneg hx hz
  have hzS : z ≤ x + z := by linarith
  have hzroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hzS hE)
  simp only [Real.sqrt_mul hE] at hzroot
  have hroot (c : ℝ) (hc : 0 ≤ c) : Real.sqrt (c * s ^ 2 * (x + z)) =
      s * Real.sqrt c * Real.sqrt (x + z) := by
    rw [show c * s ^ 2 * (x + z) = s ^ 2 * (c * (x + z)) by ring,
      Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le, Real.sqrt_mul hc]
    ring
  have hpbound := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hpS
    (mul_nonneg hC (sq_nonneg s)))
  rw [hroot C hC] at hpbound
  have heq : Real.sqrt (2 * (E * z) + 2 * (E * x)) =
      Real.sqrt (2 * E) * Real.sqrt (x + z) := by
    rw [show 2 * (E * z) + 2 * (E * x) = (2 * E) * (x + z) by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 2 * E)]
  have hvq : Real.sqrt (2 * (V * s ^ 2 * z) + 2 * (V * s ^ 2 * x)) =
      s * Real.sqrt (2 * V) * Real.sqrt (x + z) := by
    rw [show 2 * (V * s ^ 2 * z) + 2 * (V * s ^ 2 * x) = (2 * V) * s ^ 2 * (x + z) by ring]
    exact hroot (2 * V) (by positivity)
  have hfirst := mul_le_mul_of_nonneg_left hzroot (by positivity : 0 ≤ 2 * A * s)
  rw [heq, hvq, Real.sqrt_mul hE]
  dsimp only [directionRecoveryError]
  nlinarith only [hfirst, hpbound]

/-- The reciprocal length from coefficient recovery cancels the length
in the error, leaving a uniform physical direction bound. -/
theorem direction_recovery_scaled_bound {s A V E C G M x z p : ℝ}
    (hs : 0 < s) (hA : 0 ≤ A) (hV : 0 ≤ V) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hG : 0 ≤ G) (hM : 0 ≤ M) (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hp : 0 ≤ p) (hpS : p ≤ x + z) :
    let a := 4 * (G / (s / 2048))
    let err := (2 * A * s) * Real.sqrt (E * z) + Real.sqrt (C * s ^ 2 * p) +
      (A * s) * Real.sqrt (2 * (E * z) + 2 * (E * x)) +
      Real.sqrt (2 * (V * s ^ 2 * z) + 2 * (V * s ^ 2 * x)) / 4
    Real.sqrt (2 * (V * s ^ 2 * z) + 2 * (V * s ^ 2 * x)) +
      s * (2 * a * err) + 2 * (2 * M * err + (2 * s) * (2 * a * err)) ≤
      directionRecoveryConstant A V E C G M * s * Real.sqrt (x + z) := by
  intro a err
  have he := direction_recovery_scaled_error hs hA hV hE hC hx hz hp hpS
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hcoeff : 0 ≤ s * (2 * a) + 4 * M + 4 * s * (2 * a) := by positivity
  have hmul := mul_le_mul_of_nonneg_left he hcoeff
  have hroot : Real.sqrt (2 * (V * s ^ 2 * z) + 2 * (V * s ^ 2 * x)) =
      s * Real.sqrt (2 * V) * Real.sqrt (x + z) := by
    rw [show 2 * (V * s ^ 2 * z) + 2 * (V * s ^ 2 * x) = s ^ 2 * ((2 * V) * (x + z)) by ring,
      Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le,
      Real.sqrt_mul (by positivity : 0 ≤ 2 * V)]
    ring
  have hscale : (s * (2 * a) + 4 * M + 4 * s * (2 * a)) *
      (s * directionRecoveryError A V E C * Real.sqrt (x + z)) =
      (81920 * G + 4 * M) * s * directionRecoveryError A V E C * Real.sqrt (x + z) := by
    dsimp only [a]
    field_simp; ring
  rw [hscale] at hmul
  change (s * (2 * a) + 4 * M + 4 * s * (2 * a)) * err ≤ _ at hmul
  rw [hroot]
  change _ ≤ _ at hmul
  dsimp only [directionRecoveryConstant]
  nlinarith only [hmul]

end RegularPointCoordinates

end OAI
