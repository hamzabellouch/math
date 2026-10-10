import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticTree
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianAffineImage

namespace OAI

/-! Independence of the common Gaussian root and retained innovation tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma cavity_root_tree_independent {d : ℕ} (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (P Q : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n))
    [SFinite μ] [SFinite P] [SFinite Q]
    (R : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hR : Measurable R)
    (T : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n →
      NoiseTree (EuclideanSpace ℝ (Fin d)) n) (hT : Measurable T)
    (hPQ : ∀ s, P.map (fun V => T (s, V)) = Q) :
    (μ.prod P).map (fun p => (R p.1, T p)) = (μ.map R).prod Q := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hmap : Measurable (fun p : EuclideanSpace ℝ (Fin d) ×
      NoiseTree (EuclideanSpace ℝ (Fin d)) n => (R p.1, T p)) :=
    (hR.comp measurable_fst).prodMk hT
  rw [lintegral_map hF hmap,
    lintegral_prod (fun p : EuclideanSpace ℝ (Fin d) ×
      NoiseTree (EuclideanSpace ℝ (Fin d)) n => F (R p.1, T p))
      (show AEMeasurable (fun p => F (R p.1, T p)) (μ.prod P) from
        (hF.comp hmap).aemeasurable),
    lintegral_prod _ hF.aemeasurable]
  have hinner (s : EuclideanSpace ℝ (Fin d)) :
      (∫⁻ V, F (R s, T (s, V)) ∂P) = ∫⁻ V, F (R s, V) ∂Q := by
    rw [← hPQ s, lintegral_map
      (show Measurable (fun V => F (R s, V)) from
        hF.comp (measurable_const.prodMk measurable_id))
      (show Measurable (fun V => T (s, V)) from
        hT.comp (measurable_const.prodMk measurable_id))]
  simp_rw [hinner]
  exact (lintegral_map hF.lintegral_prod_right' hR).symm

/-- Root-dependent reweighting preserves the unchanged external root law.
After the deterministic root rescaling, the innovation tree is independent
of a centered Gaussian root with covariance `J₀ S₀ J₀ᵀ`. -/
theorem cavity_quadratic_root_tree_law {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef) :
    let μ := cavityGaussianMarks S
    let c := fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
    let g := fun i => cavityStepInnovation K (H i) (H (i + 1))
    let J := (1 - H 0 * K)⁻¹
    ((multivariateGaussian 0 S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _)).map
        (fun p => (Matrix.toEuclideanCLM (𝕜 := ℝ) J p.1,
          cavityInnovationTree n b μ c g p.1 p.2)) =
      (multivariateGaussian 0 (J * S₀ * J.transpose)).prod
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks (fun i =>
          (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)) : Measure _) := by
  dsimp only
  rw [cavity_root_tree_independent n
    (multivariateGaussian 0 S₀)
    (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks (fun i =>
      (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)) : Measure _)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹) (by fun_prop)
    (fun p => cavityInnovationTree n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun i => cavityStepInnovation K (H i) (H (i + 1))) p.1 p.2)
    (measurable_cavityInnovationTree n b (cavityGaussianMarks S) _ _
      (fun i => measurable_cavityQuadraticStepWeight _ _ _ _)
      (fun i => measurable_cavityStepInnovation _ _ _))
    (fun s => cavity_quadratic_innovation_tree_law n K H S b hK hH hS hb hdet hΔ hQ s)]
  congr 1
  simpa only [map_zero, zero_add] using
    cavity_multivariateGaussian_affine_image (1 - H 0 * K)⁻¹ S₀ hS₀ 0 0

end InvariantIsing

end

end OAI
