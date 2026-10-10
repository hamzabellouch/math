import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationTwoJet
import OAI.Probability.InvariantIsing.Magnetic.MagneticStationaryFamily
import OAI.Probability.InvariantIsing.Fields.FieldAffineAverageDerivative

namespace OAI

/-! Joint variance/spatial differentiation of the actual scalar
continuation. The covariance differential is left as integrals here;
Gaussian integration by parts then identifies its time generator. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticGaussianAverageDifferential (ζ v : ℝ) (F M A B : ℝ → ℝ) (z : ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  let ν := (gaussianReal 0 1).tilted (fun u => ζ * F (z + Real.sqrt v * u))
  let D := fun u => pairLinear
    (M (z + Real.sqrt v * u) * ((1 / (2 * Real.sqrt v)) * u))
    (M (z + Real.sqrt v * u))
  (∫ u, pairLinear
      (B (z + Real.sqrt v * u) * ((1 / (2 * Real.sqrt v)) * u))
      (B (z + Real.sqrt v * u)) + (ζ * A (z + Real.sqrt v * u)) • D u ∂ν) -
    (∫ u, A (z + Real.sqrt v * u) ∂ν) • (∫ u, ζ • D u ∂ν)

theorem magneticGaussianAverageTwo_hasFDerivAt (P : MagneticContinuationJet) (A : MagneticContinuationTwoJet)
    (F : ℝ → ℝ) (hF : Measurable F) (dF : ∀ z, HasDerivAt F (P.value z) z)
    (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F A.value q.2)
      (magneticGaussianAverageDifferential ζ v F P.value A.value A.first z) (v, z) := by
  obtain ⟨K, hK, bK⟩ := P.bValue
  obtain ⟨L, _, bL⟩ := P.bFirst
  obtain ⟨CA, hCA, bCA⟩ := A.bValue
  obtain ⟨CB, hCB, bCB⟩ := A.bFirst
  let I := Ioo (v / 2) (v + 1)
  let S := (magneticStationaryFamily I F P hF K L bK bL dF).toFieldSmoothFamily
  let α : (ℝ × ℝ) → ℝ → ℝ := fun q u => A.value (q.2 + Real.sqrt q.1 * u)
  let Dα : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun q u => pairLinear
    (A.first (q.2 + Real.sqrt q.1 * u) * ((1 / (2 * Real.sqrt q.1)) * u))
    (A.first (q.2 + Real.sqrt q.1 * u))
  let R := 1 / (2 * Real.sqrt (v / 2))
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hm : 0 < v / 2 := by linarith
  have hbound (q : ℝ × ℝ) (hq : q.1 ∈ I) :
      |1 / (2 * Real.sqrt q.1)| ≤ R := by
    simpa only [abs_one] using abs_div_two_sqrt_le hm hq.1.le 1
  have hdα (q : ℝ × ℝ) (hq : q.1 ∈ I) (u : ℝ) :
      HasFDerivAt (fun r => α r u) (Dα q u) q := by
    have hb (p : ℝ × ℝ) (_ : p.1 ∈ I) :
        HasFDerivAt (fun r : ℝ × ℝ => A.value r.2) (pairLinear 0 (A.first p.2)) p := by
      convert (A.dValue p.2).hasFDerivAt.comp p hasFDerivAt_snd using 1
      · rfl
      · apply ContinuousLinearMap.ext
        intro w
        simp [pairLinear, mul_comm]
    simpa only [zero_add, one_mul] using
      affine_gaussian_shift_hasFDerivAt hb 0 1 u hq (by
        dsimp only [I] at hq
        linarith [hq.1])
  have hbα (q : ℝ × ℝ) (_ : q.1 ∈ I) (u : ℝ) : |α q u| ≤ CA * (1 + |u|) := by
    exact (bCA _).trans (le_mul_of_one_le_right hCA (by linarith [abs_nonneg u]))
  have hbDα (q : ℝ × ℝ) (hq : q.1 ∈ I) (u : ℝ) :
      ‖Dα q u‖ ≤ (CB * (R + 1)) * (1 + |u|) ^ 2 := by
    refine (norm_pairLinear_le _ _).trans ?_
    have hf : |A.first (q.2 + Real.sqrt q.1 * u) * ((1 / (2 * Real.sqrt q.1)) * u)| ≤
        CB * R * |u| := by
      rw [abs_mul, abs_mul]
      exact (mul_le_mul (bCB _) (mul_le_mul_of_nonneg_right (hbound q hq) (abs_nonneg u))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hCB).trans_eq (by ring)
    have hg := bCB (q.2 + Real.sqrt q.1 * u)
    have h1 : 1 ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
    have h2 : |u| ≤ (1 + |u|) ^ 2 := by nlinarith [sq_nonneg |u|, abs_nonneg u]
    nlinarith [mul_le_mul_of_nonneg_left h1 hCB,
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hCB hR)]
  have hp : (v, z) ∈ I ×ˢ univ := ⟨by dsimp only [I]; constructor <;> linarith, mem_univ z⟩
  have hh := S.affine_average_hasFDerivAt isOpen_Ioo α Dα 0 1 ζ hm
    (fun t ht => by simpa only [zero_add, one_mul] using ht.1.le)
    (fun t ht => by simpa only [zero_add, one_mul] using ht.2.le)
    hCA (mul_nonneg hCB (by linarith : 0 ≤ R + 1))
    (fun q => A.mValue.comp (by fun_prop))
    (fun q => (measurable_pairLinear
      (A.mFirst.comp (by fun_prop) |>.mul (by fun_prop))
      (A.mFirst.comp (by fun_prop))).aestronglyMeasurable)
    hbα hbDα hdα hp.1
  simpa only [α, Dα, S, magneticStationaryFamily, FieldSmoothFamily.affineShift,
    FieldSmoothFamily.affineDifferential, fieldAmplitudeSlope, zero_add, one_mul,
    gaussianTiltAverage, magneticGaussianAverageDifferential] using hh

theorem magneticGaussianAverage_hasFDerivAt (P A : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (dF : ∀ z, HasDerivAt F (P.value z) z)
    (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F A.value q.2)
      (magneticGaussianAverageDifferential ζ v F P.value A.value A.first z) (v, z) := by
  exact magneticGaussianAverageTwo_hasFDerivAt P A.toTwoJet F hF dF ζ hv z

end InvariantIsing

end

end OAI
