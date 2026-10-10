import OAI.Geometry.RCD.Sobolev.AffineCoefficientEnergy
import OAI.Geometry.RCD.Coordinates.DyadicCovectorGrowth

namespace OAI

/-! # Affine nondegeneracy in the actual dyadic normalizing frame -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The exact normalization eight levels inward controls the coefficients
on the radial testing ball. Slow frame growth returns the estimate to the
frame used by the radial fit, with a constant independent of scale. -/
theorem dyadic_affine_coefficient {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X)
    (hgradient : LocalHarmonicL2GradientInput hX)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {a R ε : ℝ}, 0 ≤ a → 0 < R → a * (3 * R) ≤ 1 →
      BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a) →
      ∀ p : X,
      ∀ (u : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic),
      ∀ F : ℕ → Euclidean (m + 2) ≃L[ℝ] Euclidean (m + 2),
      0 ≤ ε → ((m + 2 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio (m + 1) * ε) ≤ 1 / 64 →
      (∀ i, IsExactMeanNormalization (hausdorff (m + 2) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
        (ball p (R / 2 ^ i)) measurableSet_ball (F i)) →
      (∀ i, ∃ v : X → Euclidean (m + 2),
        FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p (R / 2 ^ i) ε
          (transformedColumn (hausdorff (m + 2) X) hX.quadratic u (F i)) v) →
      ∀ i, -κ ≤ K * ((R / 2 ^ i) / 128) ^ 2 →
      ∀ (b : Euclidean (m + 2)) (w : SobolevSpace (hausdorff (m + 2) X) hX.quadratic) (c : ℝ),
      IsSobolevHarmonicOn (hausdorff (m + 2) X) hX.quadratic (ball p ((R / 2 ^ i) / 128)) w →
      SobolevSpace.toLp (hausdorff (m + 2) X) hX.quadratic
        (w - sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u b) =ᵐ[
          (hausdorff (m + 2) X).restrict (ball p ((R / 2 ^ i) / 128))] (fun _ => c) →
      ‖(F i).symm b‖ ^ 2 ≤ (C / ((R / 2 ^ i) / 128)) ^ 2 *
        ‖normalizeLocalL2 (hausdorff (m + 2) X) (ball p ((R / 2 ^ i) / 128))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (SobolevSpace.restrictLp (hausdorff (m + 2) X) hX.quadratic
            (ball p ((R / 2 ^ i) / 128)) w)‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hcoef⟩ := hgradient.affine_coefficient (by omega) hκ
  let C := C₀ * (9 / 8 : ℝ) ^ 8
  have hpow : (1 : ℝ) ≤ (9 / 8 : ℝ) ^ 8 := one_le_pow₀ (by norm_num)
  have hC : 1 ≤ C := by
    exact (show (1 : ℝ) = 1 * 1 by norm_num).trans_le
      (mul_le_mul hC₀ hpow (by norm_num) (zero_le_one.trans hC₀))
  refine ⟨C, hC, ?_⟩
  intro a R ε ha hR hscale hBG p u F hε hsmall hexact hfirst i hcurv b w c hw hc
  have hgrowth := dyadic_covector_norm_growth (m + 1) hX ha hBG u p hR hscale hε hsmall
    F hexact hfirst i 8 b
  have hrad : R / (2 : ℝ) ^ (i + 8) = ((R / 2 ^ i) / 128) / 2 := by
    rw [pow_add]
    norm_num
    ring
  have hn := hcoef p ((R / 2 ^ i) / 128) (by positivity) hcurv u (F (i + 8))
    (by rw [← hrad]; exact hexact (i + 8)) b w c hw hc
  have hsq : ‖(F i).symm b‖ ^ 2 ≤ ((9 / 8 : ℝ) ^ 8) ^ 2 * ‖(F (i + 8)).symm b‖ ^ 2 := by
    rw [← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hgrowth
  apply hsq.trans
  have hh := mul_le_mul_of_nonneg_left hn (sq_nonneg ((9 / 8 : ℝ) ^ 8))
  convert hh using 1
  dsimp only [C]
  ring

end RegularPointCoordinates

end

end OAI
