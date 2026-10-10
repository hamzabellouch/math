import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalStartingData

namespace OAI

/-! # The moving-coordinate operator represents the physical initial datum -/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

attribute [local irreducible] expandingScaleTransfer sobolevToExpanding

theorem physicalStartingOperator_function (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : Radius) (θ : ℝ) (x y : SchrodingerTorus) (f : FourierL2) :
    expandingTorusFunction a k L.1 (physicalStartingOperator a k ha hk L θ x f) y =
      physicalStartingAmplitude a L θ * sobolevTorusFunction k f (x + y) := by
  let v := sobolevToExpanding a k ha hk (sobolevTranslation x f)
  have he : expandingTorusFunction a k 1 v y =
      sobolevTorusFunction k (sobolevTranslation x f) y := by
    rw [← sobolevTorusFunction_expandingToSobolev a k ha ha1 hk]
    exact congrArg (fun g => sobolevTorusFunction k g y)
      (expandingToSobolev_sobolevToExpanding a k ha ha1 hk (sobolevTranslation x f))
  change expandingTorusFunction a k L.1
    (physicalStartingAmplitude a L θ • expandingScaleTransfer a k 1 L.1 ha hk le_rfl L.2 v) y = _
  rw [expandingTorusFunction_eq_evaluation a k L.1 ha ha1 hk L.2,
    map_smul, smul_eq_mul]
  congr 1
  rw [← expandingTorusFunction_eq_evaluation a k L.1 ha ha1 hk L.2,
    expandingScaleTransfer_function a k 1 L.1 ha ha1 hk le_rfl L.2, he,
    sobolevTorusFunction_translation k (by linarith) x y f]

noncomputable def physicalReferenceData (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (L : Radius) : FourierL2 :=
  (L.1 ^ (2 * a) : ℝ) • expandingToSobolev a k ha1 hk
    (expandingInverseTransfer a k L.1 ha hk L.2
      (sampledCutoffProfileAtRadius a k ha1 hk χ hχ Q hQ L))

theorem physicalStartingPerturbation_reference (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (L : Radius) :
    physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ L 0 0
      (physicalReferenceData a k ha ha1 hk χ hχ Q hQ L) = 0 := by
  let q := sampledCutoffProfileAtRadius a k ha1 hk χ hχ Q hQ L
  have hInv : expandingScaleTransfer a k 1 L.1 ha hk le_rfl L.2
      (expandingInverseTransfer a k L.1 ha hk L.2 q) = q :=
    congrArg (fun A : FourierL2 →L[ℂ] FourierL2 => A q)
      (expandingWeightUnit a k L.1 ha hk L.2).val_inv
  have hp : L.1 ^ (-2 * a) * L.1 ^ (2 * a) = 1 := by
    rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one L.2)]
    simp
  change physicalStartingAmplitude a L 0 •
    expandingScaleTransfer a k 1 L.1 ha hk le_rfl L.2
      (sobolevToExpanding a k ha hk (sobolevTranslation 0
        ((L.1 ^ (2 * a) : ℝ) • expandingToSobolev a k ha1 hk
          (expandingInverseTransfer a k L.1 ha hk L.2 q)))) - q = 0
  rw [sobolevTranslation_zero, ContinuousLinearMap.map_smul_of_tower,
    sobolevToExpanding_expandingToSobolev, ContinuousLinearMap.map_smul_of_tower, hInv]
  simp only [physicalStartingAmplitude, neg_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_mul]
  rw [← IsScalarTower.algebraMap_smul ℂ (L.1 ^ (2 * a)) q, smul_smul]
  change ((L.1 ^ (-2 * a) : ℝ) * (L.1 ^ (2 * a) : ℝ) : ℂ) • q - q = 0
  rw [← Complex.ofReal_mul, hp, Complex.ofReal_one, one_smul, sub_self]

end DefocusingNLS

end OAI
