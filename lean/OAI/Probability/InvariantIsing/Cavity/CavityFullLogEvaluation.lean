import OAI.Probability.InvariantIsing.Cavity.CavityLinearLogEvaluation
import OAI.Probability.InvariantIsing.Cavity.CavityRootedReplicaTransport

namespace OAI

/-! The full quadratic cavity logarithmic mean follows from the actual
innovation law and scalar field mean, including all normalizer terms. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator NNReal BigOperators

namespace InvariantIsing

theorem cavity_full_log_evaluation {d k : ℕ} (hk : 0 < k) (h : FieldStep)
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
    (v : ℝ≥0)
    (hcov : ∀ i < h.depth,
      L.transpose * ((1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) * L =
        (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * cavityResolvent K (H h.depth) * L = (v : ℝ) • 1)
    (hroot : L.transpose * ((1 - H 0 * K)⁻¹ * S₀ * ((1 - H 0 * K)⁻¹).transpose) * L =
      h.height 0 • 1) :
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) h.depth (chainExponent h.cut)
        (cavityGaussianMarks S) : Measure _)
    let F := cavityRootedLogNormalizer h.depth K (H h.depth) L (c • 1) (uniformSpinPrior k)
    Integrable F P ∧ (∫ p, F p ∂P) =
      Matrix.trace (S₀ * cavityBackwardQuadratic K (H 0)) / 2 -
        (∑ j ∈ Finset.range h.depth, cavityDeterminantStep K H (chainExponent h.cut) j) -
        Real.log (1 - H h.depth * K).det / 2 +
        (k : ℝ) * (c + v) / 2 +
        ∫ z, cascadeRecursion h.depth (chainExponent h.cut)
          (fun i => vectorGaussianLaw k (fieldStepVariance h i))
          (fun _ p => p.1 + p.2) (fun y => ∑ i, Real.log (Real.cosh (y i))) z
          ∂(vectorGaussianLaw k (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure _) := by
  intro P F
  let b := chainExponent h.cut
  let S' := fun i => (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose
  let S₀' := (1 - H 0 * K)⁻¹ * S₀ * ((1 - H 0 * K)⁻¹).transpose
  let R := cavityResolvent K (H h.depth)
  let P' := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀').prod
    (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) h.depth b (cavityGaussianMarks S') :
      Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) h.depth))
  let F' := cavityRootedLogNormalizer h.depth 0 R L (c • 1) (uniformSpinPrior k)
  let T := cavitySpinDisorderInnovation h.depth K H S b
  let Z := fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) h.depth =>
    Real.log (cavityResidualPartition h.depth K (H h.depth) p.1 p.2).toReal
  have hbC := chainExponent_admissible h.ordered_cut h.first h.last
  have hS' (i : ℕ) : (S' i).PosSemidef :=
    cavity_innovation_covariance_posSemidef K (H i) (H (i + 1)) (S i) (hS i)
      (b i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i)
  have hS₀' : S₀'.PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS₀.mul_mul_conjTranspose_same (1 - H 0 * K)⁻¹
  have hR' : R.PosSemidef := cavity_tilt_covariance_posSemidef K (H h.depth) hR hQR
  have hlinear := cavity_linear_rooted_log_integral hk h S' hS' R hR' S₀' hS₀'
    L v hcov hres hroot c
  have hquad := cavity_residual_partition_log_integral h.depth K H S b S₀ hS₀ hbC
    hK hH hS hb hdet hΔ hQ hR hQR
  have hTP : MeasurePreserving T P P' :=
    ⟨measurable_cavitySpinDisorderInnovation h.depth K H S b,
      cavity_quadratic_root_tree_law h.depth K H S b S₀ hS₀ hK hH hS hb hdet hΔ hQ⟩
  have hdata := cavity_rooted_full_integrability h.depth K H S b S₀ hS₀ L (c • 1) hbC
    hK hH hS hb hdet hΔ hQ hR hQR (uniformSpinPrior k : Measure (Spin k))
  have hreg : ∀ᵐ p ∂P, NoiseGibbsRegular h.depth b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ x => x.1 + x.2) p.1 p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_noiseGibbsRegular h.depth b
      (cavityGaussianMarks S) (fun i => measurable_cavityQuadraticStepWeight _ _ _ _)
      (fun _ => measurable_fst.add measurable_snd))).mpr
    exact Filter.Eventually.of_forall (fun s =>
      cavity_quadratic_regular_ae h.depth K H S b hbC hK hH hS hb hdet hΔ hQ s)
  have he : F =ᵐ[P] fun p => Z p + F' (T p) := by
    filter_upwards [hdata, hreg] with p hp hr
    exact cavity_full_log_normalizer_transport h.depth K H S b L (c • 1) hK hR
      (hdet h.depth) hQR p.1 p.2 hp.1 hr (uniformSpinPrior k) hp.2
  have hi : Integrable (fun p => Z p + F' (T p)) P :=
    hquad.1.add (hTP.integrable_comp_of_integrable hlinear.1)
  refine ⟨hi.congr he.symm, ?_⟩
  have hZi : Integrable Z P := hquad.1
  have hFi : Integrable (fun p => F' (T p)) P := hTP.integrable_comp_of_integrable hlinear.1
  have hmap : (∫ p, F' (T p) ∂P) = ∫ p, F' p ∂P' :=
    hTP.hasLaw.integral_comp (measurable_cavityRootedLogNormalizer _ _ _ _ _ _).aestronglyMeasurable
  rw [integral_congr_ae he, integral_add hZi hFi, hmap]
  dsimp only [Z, F', P', P]
  rw [hquad.2, hlinear.2]
  ring

end InvariantIsing

end

end OAI
