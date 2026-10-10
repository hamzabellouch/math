import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPolynomial

namespace OAI

/-! # Polynomial identities in the physical unit-torus realization -/

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)

variable (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)

theorem expandingUnitTorusFunction_product (f g : FourierL2) :
    expandingUnitTorusFunction a k L (expandingProduct a k L ha ha1 hk hL f g) =
      expandingUnitTorusFunction a k L f * expandingUnitTorusFunction a k L g := by
  ext t
  obtain ⟨x, rfl⟩ := unitTorusProjection_isOpenQuotientMap.surjective t
  simp only [ContinuousMap.mul_apply, expandingUnitTorusFunction_projection a k L ha ha1 hk hL,
    expandingTorusFunction_product a k L ha ha1 hk hL]

include ha ha1 hk hL in
theorem expandingUnitTorusFunction_smul (c : ℂ) (f : FourierL2) :
    expandingUnitTorusFunction a k L (c • f) = c • expandingUnitTorusFunction a k L f := by
  ext t
  obtain ⟨x, rfl⟩ := unitTorusProjection_isOpenQuotientMap.surjective t
  simp only [ContinuousMap.smul_apply, expandingUnitTorusFunction_projection a k L ha ha1 hk hL,
    expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL, map_smul]

include ha ha1 hk hL in
theorem expandingUnitTorusFunction_conjugate (f : FourierL2) :
    expandingUnitTorusFunction a k L (fourierConjugate f) = star (expandingUnitTorusFunction a k L f) := by
  ext t
  obtain ⟨x, rfl⟩ := unitTorusProjection_isOpenQuotientMap.surjective t
  simp only [ContinuousMap.star_apply, expandingUnitTorusFunction_projection a k L ha ha1 hk hL,
    expandingTorusFunction_conjugate a k L ha ha1 hk hL, starRingEnd_apply]

theorem expandingUnitTorusFunction_power (f : FourierL2) (m : ℕ) :
    expandingUnitTorusFunction a k L (expandingPower a k L ha ha1 hk hL f m) =
      (expandingUnitTorusFunction a k L f) ^ m := by
  ext t
  obtain ⟨x, rfl⟩ := unitTorusProjection_isOpenQuotientMap.surjective t
  simp only [ContinuousMap.pow_apply, expandingUnitTorusFunction_projection a k L ha ha1 hk hL,
    expandingPower_function a k L ha ha1 hk hL]

theorem expandingCircular_unit (m : ℕ) (q : FourierL2) (t : T) :
    expandingUnitTorusFunction a k L (expandingCircularCoefficient a k L ha ha1 hk hL m q) t =
      ((m + 1 : ℕ) : ℂ) * (expandingUnitTorusFunction a k L q t) ^ m *
        star (expandingUnitTorusFunction a k L q t) ^ m := by
  simp only [expandingCircularCoefficient, expandingUnitTorusFunction_smul a k L ha ha1 hk hL,
    expandingUnitTorusFunction_product a k L ha ha1 hk hL,
    expandingUnitTorusFunction_power a k L ha ha1 hk hL,
    expandingUnitTorusFunction_conjugate a k L ha ha1 hk hL,
    ContinuousMap.smul_apply, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
    ContinuousMap.star_apply, smul_eq_mul]
  ring

theorem expandingAnticircular_unit (m : ℕ) (q : FourierL2) (t : T) :
    expandingUnitTorusFunction a k L (expandingAnticircularCoefficient a k L ha ha1 hk hL m q) t =
      (m : ℂ) * (expandingUnitTorusFunction a k L q t) ^ (m + 1) *
        star (expandingUnitTorusFunction a k L q t) ^ (m - 1) := by
  simp only [expandingAnticircularCoefficient, expandingUnitTorusFunction_smul a k L ha ha1 hk hL,
    expandingUnitTorusFunction_product a k L ha ha1 hk hL,
    expandingUnitTorusFunction_power a k L ha ha1 hk hL,
    expandingUnitTorusFunction_conjugate a k L ha ha1 hk hL,
    ContinuousMap.smul_apply, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
    ContinuousMap.star_apply, smul_eq_mul]
  ring

end DefocusingNLS

end OAI
