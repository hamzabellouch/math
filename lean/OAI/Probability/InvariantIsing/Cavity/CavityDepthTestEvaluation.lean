import OAI.Probability.InvariantIsing.Cavity.CavitySpinTestEvaluation
import OAI.Probability.InvariantIsing.Cavity.CavityLinearNoiseDepth

namespace OAI

/-! The quadratic cavity tilt preserves the common-level distribution. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator NNReal

namespace InvariantIsing

theorem cavity_full_depth_test_evaluation (hpub : PanchenkoTalagrandFieldPairInput)
    {d k : ℕ} (hk : 0 < k) (h : FieldStep)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (c : ℝ)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef)
    (hb : ∀ i, 0 < chainExponent h.cut i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = chainExponent h.cut i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (chainExponent h.cut i • cavityBackwardQuadratic K (H (i + 1)))
        (CFC.sqrt (S i))).PosDef)
    (hR : (H h.depth).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H h.depth))).PosDef)
    (hAtom : ∀ i < h.depth,
      NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i)))
    (v : ℝ≥0)
    (hcov : ∀ i < h.depth,
      L.transpose * ((1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) * L =
        (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * cavityResolvent K (H h.depth) * L = (v : ℝ) • 1)
    (ψ : ℕ → ℝ)
    {B : ℝ} (hψ : ∀ i, |ψ i| ≤ B) :
    (∫ σ, cavityRootedDepthTest ψ σ
      ∂((probabilityReplicaKernel
        (cavityRootedFullGibbs h.depth K (H h.depth) L (c • 1) (uniformSpinPrior k))
        (cavityRootedFullGibbs h.depth K (H h.depth) L (c • 1) (uniformSpinPrior k)).measurable)
          ∘ₘ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
            (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) h.depth (chainExponent h.cut)
              (cavityGaussianMarks S) : Measure _))) =
      ∫ t, ψ (fieldLevelIndex h t).val ∂pathMeasure := by
  let b := chainExponent h.cut
  let S' := fun i => (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose
  let S₀' := (1 - H 0 * K)⁻¹ * S₀ * ((1 - H 0 * K)⁻¹).transpose
  let R := cavityResolvent K (H h.depth)
  have hbC := chainExponent_admissible h.ordered_cut h.first h.last
  have hS' (i : ℕ) : (S' i).PosSemidef :=
    cavity_innovation_covariance_posSemidef K (H i) (H (i + 1)) (S i) (hS i)
      (b i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i)
  have hR' : R.PosSemidef := cavity_tilt_covariance_posSemidef K (H h.depth) hR hQR
  have hAtom' (i : ℕ) (hi : i < h.depth) :
      NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S' i)) := by
    let := hAtom i hi
    exact cavity_quadratic_innovation_nullSingleton K (H i) (H (i + 1)) (S i)
      hK (hH (i + 1)) (hS i) (b i) (hb i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i)
  rw [cavity_rooted_depth_test_transport h.depth K H S b S₀ hS₀ L (c • 1)
    hbC hK hH hS hb hdet hΔ hQ hR hQR (uniformSpinPrior k)]
  rw [cavity_rooted_depth_test_product_disintegration h.depth 0 R L (c • 1)
    (uniformSpinPrior k) (multivariateGaussian 0 S₀')
    (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) h.depth b (cavityGaussianMarks S') : Measure _)
    ψ hψ]
  trans (∫ _s : EuclideanSpace ℝ (Fin d), (∫ t, ψ (fieldLevelIndex h t).val ∂pathMeasure)
    ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀')
  · apply integral_congr_ae
    exact ae_of_all _ (fun s => cavity_linear_rooted_depth_evaluation hpub hk h S' hS' hAtom' R hR'
      L v hcov hres c s ψ hψ)
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

end InvariantIsing

end

end OAI
