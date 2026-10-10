import OAI.Probability.InvariantIsing.Magnetic.MagneticGaussianCovariance
import OAI.Probability.InvariantIsing.Fields.FieldSpinLinear

namespace OAI

/-! The exact heat generator of the scalar continuation. Integration by
parts removes the apparent inverse square-root singularity from the
positive-variance differential. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticGaussianGenerator (ζ v : ℝ) (F M Q A B C : ℝ → ℝ) (z : ℝ) : ℝ :=
  let T := fun f => gaussianTiltAverage v ζ F f z
  T C / 2 + ζ * T (fun y => B y * M y) +
    ζ / 2 * (T (fun y => A y * Q y) - T A * T Q) +
    ζ ^ 2 / 2 * (T (fun y => A y * (M y) ^ 2) - T A * T (fun y => (M y) ^ 2))

lemma magneticGaussianTimeTwo_eq_generator (P : MagneticContinuationJet) (A : MagneticContinuationTwoJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    magneticGaussianTime ζ v F P.value A.value A.first z =
      magneticGaussianGenerator ζ v F P.value P.first A.value A.first A.second z := by
  let r := Real.sqrt v
  let ν := (gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))
  obtain ⟨KM, _, bM⟩ := P.bValue
  obtain ⟨KQ, _, bQ⟩ := P.bFirst
  obtain ⟨KA, hKA, bA⟩ := A.bValue
  obtain ⟨KB, hKB, bB⟩ := A.bFirst
  obtain ⟨KC, _, bC⟩ := A.bSecond
  have hr : r ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have bAM (y : ℝ) : |A.value y * P.value y| ≤ KA * KM := by
    rw [abs_mul]
    exact mul_le_mul (bA y) (bM y) (abs_nonneg _) hKA
  have bBM (y : ℝ) : |A.first y * P.value y| ≤ KB * KM := by
    rw [abs_mul]
    exact mul_le_mul (bB y) (bM y) (abs_nonneg _) hKB
  have bAQ (y : ℝ) : |A.value y * P.first y| ≤ KA * KQ := by
    rw [abs_mul]
    exact mul_le_mul (bA y) (bQ y) (abs_nonneg _) hKA
  have bdAM (y : ℝ) : |A.first y * P.value y + A.value y * P.first y| ≤
      KB * KM + KA * KQ := (abs_add_le _ _).trans (add_le_add (bBM y) (bAQ y))
  have iBM : Integrable (fun u => A.first (z + r * u) * P.value (z + r * u)) ν :=
    magnetic_tilted_shift_integrable hF hG (A.mFirst.mul P.mValue) bBM r ζ z
  have iAQ : Integrable (fun u => A.value (z + r * u) * P.first (z + r * u)) ν :=
    magnetic_tilted_shift_integrable hF hG (A.mValue.mul P.mFirst) bAQ r ζ z
  have hB := magnetic_tilted_scaled_test_ibp hF hG P.mValue A.mFirst A.mSecond
    bM bB bC dF A.dFirst hr ζ z
  have hM := magnetic_tilted_scaled_test_ibp hF hG P.mValue P.mValue P.mFirst
    bM bM bQ dF P.dValue hr ζ z
  have hAM := magnetic_tilted_scaled_test_ibp hF hG P.mValue
    (A.mValue.mul P.mValue) ((A.mFirst.mul P.mValue).add (A.mValue.mul P.mFirst))
    bM bAM bdAM dF (fun y => (A.dValue y).mul (P.dValue y)) hr ζ z
  dsimp only [Pi.mul_apply, Pi.add_apply] at hAM
  have hAMleft : (∫ u, A.value (z + r * u) *
      (P.value (z + r * u) * ((1 / (2 * r)) * u)) ∂ν) =
      (∫ u, (A.value (z + r * u) * P.value (z + r * u)) *
        ((1 / (2 * r)) * u) ∂ν) := by
    congr 1
    funext u
    ring
  have hAMright : (∫ u, (A.value (z + r * u) * P.value (z + r * u)) *
      P.value (z + r * u) ∂ν) =
      ∫ u, A.value (z + r * u) * (P.value (z + r * u)) ^ 2 ∂ν := by
    congr 1
    funext u
    ring
  have hMright : (∫ u, P.value (z + r * u) * P.value (z + r * u) ∂ν) =
      ∫ u, (P.value (z + r * u)) ^ 2 ∂ν := by
    congr 1
    funext u
    ring
  change magneticGaussianTime ζ v F P.value A.value A.first z = _
  dsimp only [magneticGaussianTime]
  rw [hB, hAMleft, hAM, hM, hAMright, hMright, integral_add iBM iAQ]
  dsimp only [magneticGaussianGenerator, gaussianTiltAverage]
  ring

lemma magneticContinuation_secondTwo_generator (P : MagneticContinuationJet) (A : MagneticContinuationTwoJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (ζ : ℝ) (v : ℝ≥0) (z : ℝ) :
    magneticContinuationSecond ζ v F P.value P.first A.value A.first A.second z / 2 +
        ζ * fieldSpinTransition ζ v F P.value z *
          fieldTiltSpatial ζ v F P.value A.value A.first z =
      (let T := fun f => fieldSpinTransition ζ v F f z
       T A.second / 2 + ζ * T (fun y => A.first y * P.value y) +
         ζ / 2 * (T (fun y => A.value y * P.first y) - T A.value * T P.first) +
         ζ ^ 2 / 2 * (T (fun y => A.value y * (P.value y) ^ 2) -
           T A.value * T (fun y => (P.value y) ^ 2))) := by
  obtain ⟨KM, _, bM⟩ := P.bValue
  obtain ⟨KQ, _, bQ⟩ := P.bFirst
  obtain ⟨KA, hKA, bA⟩ := A.bValue
  obtain ⟨KB, hKB, bB⟩ := A.bFirst
  have bBM (y : ℝ) : |A.first y * P.value y| ≤ KB * KM := by
    rw [abs_mul]
    exact mul_le_mul (bB y) (bM y) (abs_nonneg _) hKB
  have bAQ (y : ℝ) : |A.value y * P.first y| ≤ KA * KQ := by
    rw [abs_mul]
    exact mul_le_mul (bA y) (bQ y) (abs_nonneg _) hKA
  have hadd := fieldSpinTransition_add ζ v hF hG (A.mFirst.mul P.mValue)
    (A.mValue.mul P.mFirst) bBM bAQ z
  change fieldSpinTransition ζ v F (fun y => A.first y * P.value y + A.value y * P.first y) z =
    fieldSpinTransition ζ v F (fun y => A.first y * P.value y) z +
      fieldSpinTransition ζ v F (fun y => A.value y * P.first y) z at hadd
  have hassoc : (fun y => (A.value y * P.value y) * P.value y) =
      (fun y => A.value y * (P.value y) ^ 2) := by
    funext y
    ring
  have hsquare : (fun y => P.value y * P.value y) = (fun y => (P.value y) ^ 2) := by
    funext y
    ring
  dsimp only [magneticContinuationSecond, fieldTiltSpatial]
  rw [hadd, hassoc, hsquare]
  ring

lemma magneticGaussianTime_eq_generator (P A : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    magneticGaussianTime ζ v F P.value A.value A.first z =
      magneticGaussianGenerator ζ v F P.value P.first A.value A.first A.second z := by
  exact magneticGaussianTimeTwo_eq_generator P A.toTwoJet F hF hG dF ζ hv z

lemma magneticContinuation_second_generator (P A : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (ζ : ℝ) (v : ℝ≥0) (z : ℝ) :
    magneticContinuationSecond ζ v F P.value P.first A.value A.first A.second z / 2 +
        ζ * fieldSpinTransition ζ v F P.value z *
          fieldTiltSpatial ζ v F P.value A.value A.first z =
      (let T := fun f => fieldSpinTransition ζ v F f z
       T A.second / 2 + ζ * T (fun y => A.first y * P.value y) +
         ζ / 2 * (T (fun y => A.value y * P.first y) - T A.value * T P.first) +
         ζ ^ 2 / 2 * (T (fun y => A.value y * (P.value y) ^ 2) -
           T A.value * T (fun y => (P.value y) ^ 2))) := by
  exact magneticContinuation_secondTwo_generator P A.toTwoJet F hF hG ζ v z

end InvariantIsing

end

end OAI
