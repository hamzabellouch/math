import OAI.Probability.InvariantIsing.Magnetic.MagneticGaussianMoments
import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationTime
import OAI.Probability.InvariantIsing.Fields.FieldSecondCovariance

namespace OAI

/-! Scalar-coordinate form of the actual joint Gaussian continuation
differential. All integrability is supplied by bounded finite-spin jets. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticGaussianTime (ζ v : ℝ) (F M A B : ℝ → ℝ) (z : ℝ) : ℝ :=
  let ν := (gaussianReal 0 1).tilted (fun u => ζ * F (z + Real.sqrt v * u))
  (∫ u, B (z + Real.sqrt v * u) * ((1 / (2 * Real.sqrt v)) * u) ∂ν) +
    ζ * ((∫ u, A (z + Real.sqrt v * u) *
      (M (z + Real.sqrt v * u) * ((1 / (2 * Real.sqrt v)) * u)) ∂ν) -
      (∫ u, A (z + Real.sqrt v * u) ∂ν) *
        (∫ u, M (z + Real.sqrt v * u) * ((1 / (2 * Real.sqrt v)) * u) ∂ν))

def magneticGaussianSpace (ζ v : ℝ) (F M A B : ℝ → ℝ) (z : ℝ) : ℝ :=
  gaussianTiltAverage v ζ F B z + ζ *
    (gaussianTiltAverage v ζ F (fun y => A y * M y) z -
      gaussianTiltAverage v ζ F A z * gaussianTiltAverage v ζ F M z)

lemma magneticGaussianAverageDifferentialTwo_eq_pair (P : MagneticContinuationJet) (A : MagneticContinuationTwoJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (ζ v z : ℝ) :
    magneticGaussianAverageDifferential ζ v F P.value A.value A.first z =
      pairLinear (magneticGaussianTime ζ v F P.value A.value A.first z)
        (magneticGaussianSpace ζ v F P.value A.value A.first z) := by
  let r := Real.sqrt v
  let c := 1 / (2 * r)
  let ν := (gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))
  obtain ⟨KM, _, bM⟩ := P.bValue
  obtain ⟨KA, hKA, bA⟩ := A.bValue
  obtain ⟨KB, _, bB⟩ := A.bFirst
  have bAM (y : ℝ) : |A.value y * P.value y| ≤ KA * KM := by
    rw [abs_mul]
    exact mul_le_mul (bA y) (bM y) (abs_nonneg _) hKA
  have iB : Integrable (fun u => A.first (z + r * u)) ν :=
    magnetic_tilted_shift_integrable hF hG A.mFirst bB r ζ z
  have iM : Integrable (fun u => P.value (z + r * u)) ν :=
    magnetic_tilted_shift_integrable hF hG P.mValue bM r ζ z
  have iAM : Integrable (fun u => A.value (z + r * u) * P.value (z + r * u)) ν :=
    magnetic_tilted_shift_integrable hF hG (A.mValue.mul P.mValue) bAM r ζ z
  have linear {a : ℝ → ℝ} (ha : Measurable a) {K : ℝ} (ba : ∀ y, |a y| ≤ K) :
      Integrable (fun u => a (z + r * u) * (c * u)) ν := by
    have hi := (magnetic_tilted_linear_integrable hF hG ha ba r ζ z).const_mul c
    convert hi using 1
    funext u
    ring
  have iBt := linear A.mFirst bB
  have iMt := linear P.mValue bM
  have iAMt : Integrable (fun u => A.value (z + r * u) *
      (P.value (z + r * u) * (c * u))) ν := by
    convert linear (A.mValue.mul P.mValue) bAM using 1
    funext u
    dsimp only [Pi.mul_apply]
    ring
  exact field_pair_covariance ν ζ (fun u => A.value (z + r * u))
    (fun u => A.first (z + r * u) * (c * u)) (fun u => A.first (z + r * u))
    (fun u => P.value (z + r * u) * (c * u)) (fun u => P.value (z + r * u))
    iBt iB iMt iM iAMt iAM

lemma magneticGaussianAverageDifferential_eq_pair (P A : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (ζ v z : ℝ) :
    magneticGaussianAverageDifferential ζ v F P.value A.value A.first z =
      pairLinear (magneticGaussianTime ζ v F P.value A.value A.first z)
        (magneticGaussianSpace ζ v F P.value A.value A.first z) := by
  exact magneticGaussianAverageDifferentialTwo_eq_pair P A.toTwoJet F hF hG ζ v z

end InvariantIsing

end

end OAI
