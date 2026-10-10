import OAI.Combinatorics.Progressions.Probability.CoefficientJetDensityFactors

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem coefficientImage_retained_grid_error {K Z Y : Type*} [Fintype K]
    {O J : K → Type*} [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
    [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    [MeasurableSpace Z] [MeasurableSpace Y]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (A : ∀ k, Matrix (O k) (J k) ℤ) (s : ∀ k, O k ↪ J k)
    (hA : ∀ k, ((A k).submatrix id (s k)).det ≠ 0)
    (S : ∀ k, J k → ℝ) (P : ∀ k, O k → ℝ)
    (hS : ∀ k j, 0 < S k j) (hP : ∀ k i, 0 < P k i) (hP1 : ∀ k i, 1 ≤ P k i)
    (f : ∀ k, (J k → ℝ) → ℝ) (hf0 : ∀ k x, 0 ≤ f k x) (R T E : K → ℝ)
    (hs : ∀ k x, R k < ‖x‖ → f k x = 0)
    (hZ : ∀ k, 0 < coefficientWeightSum (f k) (S k)) (hT : ∀ k, 0 ≤ T k)
    (hdiscrete : ∀ k, ‖matrixSupCLM (normalizedIntegerColumns (A k) (S k) (P k))‖ * R k ≤ T k)
    (hcontinuous : ∀ k, (‖matrixSupCLM (normalizedIntegerPivot
        ((A k).submatrix id (s k)) (fun i => S k (s k i)) (P k))‖ +
      ‖matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (A k) (s k))
        (fun j => S k j.val) (P k))‖) * R k ≤ T k)
    (he : ∀ k v, |(∏ i, P k i) *
        (coefficientImagePMF (A k) (f k) (hf0 k) (S k) (hS k) (hs k) (hZ k) v).toReal -
      coefficientImageMask (A k) (P k)
        (selectedCoefficientDensity (A k) (s k) (hA k) (S k) (P k) (hS k) (hP k) (f k)) v|
        ≤ E k)
    (hsmall : (∑ k, (2 * T k + 1) ^ Fintype.card (O k) * E k) ≤ 1)
    (F : Z × (∀ k, O k → ℤ) → Y) (hF : Measurable F)
    (φ : Y → ℝ) (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, ‖φ y‖ ≤ B) :
    |(∫ y, φ y ∂(μ.prod (Measure.pi (fun k =>
        (coefficientImagePMF (A k) (f k) (hf0 k) (S k) (hS k) (hs k) (hZ k)).toMeasure))).map F) -
      ∫ y, φ y ∂(μ.prod (realDensityMeasure
        (Measure.pi (fun k => (Measure.count : Measure (O k → ℤ))))
        (fun x => ∏ k, coefficientGridProxy (A k) (s k) (hA k) (S k) (P k)
          (hS k) (hP k) (f k) (x k)))).map F| ≤
      B * (2 * ∑ k, (2 * T k + 1) ^ Fintype.card (O k) * E k) := by
  apply independentPMF_retained_grid_error μ _ _
    (fun k => coefficientGridProxy_integrable (A k) (s k) (hA k) (S k) (P k)
      (hS k) (hP k) (f k) (hs k) (hcontinuous k))
    (fun k => coefficientGridProxy_nonneg (A k) (s k) (hA k) (S k) (P k)
      (hS k) (hP k) (f k) (hf0 k))
    _ _ hsmall F hF φ hφ hB hb
  intro k
  exact coefficientImage_count_error (A k) (s k) (hA k) (S k) (P k)
    (hS k) (hP k) (hP1 k) (f k) (hf0 k) (hs k) (hZ k) (hT k)
    (hdiscrete k) (hcontinuous k) (he k)

end Erdos3

end

end OAI
