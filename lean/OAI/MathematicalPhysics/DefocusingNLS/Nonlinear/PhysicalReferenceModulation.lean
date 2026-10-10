import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalStartingFunction
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalModulationTaylor

namespace OAI

/-! # The modulation chart represents the actual physical reference data -/

open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem sobolevToExpanding_translation (a k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (x : SchrodingerTorus) (f : FourierL2) :
    sobolevToExpanding a k ha hk (sobolevTranslation x f) =
      sobolevTranslation x (sobolevToExpanding a k ha hk f) := by
  ext n
  simp only [sobolevToExpanding_apply, sobolevTranslation_apply]
  ring

theorem expandingScaleTransfer_translation (a k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (L M : Radius) (hLM : L.1 ≤ M.1) (x : SchrodingerTorus) (f : FourierL2) :
    expandingScaleTransfer a k L.1 M.1 ha hk L.2 hLM (sobolevTranslation x f) =
      sobolevTranslation x (expandingScaleTransfer a k L.1 M.1 ha hk L.2 hLM f) := by
  ext n
  change (expandingScaleRatio a k L.1 M.1 n : ℂ) *
      (torusCharacter n x * f n) = torusCharacter n x *
      ((expandingScaleRatio a k L.1 M.1 n : ℂ) * f n)
  ring

theorem physicalStartingOperator_reference_modulation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (M R : Radius) (θ : ℝ) (x : SchrodingerTorus) :
    physicalStartingOperator a k ha hk M θ x
        (physicalReferenceData a k ha ha1 hk χ hχ Q hQ R) =
      (physicalStartingAmplitude a M θ * (R.1 ^ (2 * a) : ℝ)) •
        sobolevTranslation x (fixedCutoffProfile a k ha ha1 hk M χ hχ Q hQ R.1) := by
  unfold physicalStartingOperator physicalReferenceData
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,
    ContinuousLinearMap.map_smul_of_tower, sobolevToExpanding_translation,
    sobolevToExpanding_expandingToSobolev,
    expandingScaleTransfer_translation a k ha hk ⟨1, le_rfl⟩ M M.2]
  rw [fixedCutoffProfile_eq_transfer]
  change physicalStartingAmplitude a M θ •
      ((R.1 ^ (2 * a) : ℝ) • sobolevTranslation x
        (expandingNearbyTransfer a k ha hk R M
          (sampledCutoffProfileAtRadius a k ha1 hk χ hχ Q hQ R))) = _
  rw [← IsScalarTower.algebraMap_smul ℂ (R.1 ^ (2 * a)), smul_smul]
  rfl

theorem physicalStartingAmplitude_expandingRadius (a : ℝ) (M R : Radius)
    (t θ : ℝ) (hR : R.1 = expandingRadius M.1 t) :
    physicalStartingAmplitude a M θ * (R.1 ^ (2 * a) : ℝ) =
      Complex.exp ((a * t : ℝ) - (θ : ℂ) * Complex.I) := by
  have hM : 0 < M.1 := lt_of_lt_of_le zero_lt_one M.2
  have hp : M.1 ^ (-2 * a) * R.1 ^ (2 * a) = Real.exp (a * t) := by
    rw [hR, expandingRadius, Real.mul_rpow hM.le (Real.exp_pos _).le,
      ← mul_assoc, ← Real.rpow_add hM, ← Real.exp_mul]
    simp only [neg_mul, neg_add_cancel, Real.rpow_zero, one_mul]
    congr 1
    ring
  unfold physicalStartingAmplitude
  rw [mul_assoc, ← Complex.ofReal_mul, hp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem physicalStartingPerturbation_reference_modulation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (M R : Radius) (p : ProfileSymmetryParameters)
    (hR : R.1 = expandingRadius M.1 p.2.2) :
    physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ M p.1
        (euclideanToTorus ((1 / M.1) • p.2.1))
        (physicalReferenceData a k ha ha1 hk χ hχ Q hQ R) =
      modulatedCutoffProfile a k ha ha1 hk χ hχ Q hQ M p := by
  unfold physicalStartingPerturbation modulatedCutoffProfile
  rw [physicalStartingOperator_reference_modulation,
    physicalStartingAmplitude_expandingRadius a M R p.2.2 p.1 hR, hR,
    fixedCutoffProfile_self]
  rfl

end DefocusingNLS

end OAI
