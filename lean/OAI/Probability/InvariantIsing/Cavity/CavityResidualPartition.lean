import OAI.Probability.InvariantIsing.Cavity.CavityResidualNormalizer

namespace OAI

/-! The residual-integrated partition function in `cav:q-constants`. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

/-- The final Gaussian integral is an ordinary residual at each leaf,
not an additional Poisson level. -/
def cavityResidualPartition {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) : ℝ≥0∞ :=
  ∫⁻ v, ∫⁻ z : EuclideanSpace ℝ (Fin d),
    ENNReal.ofReal (Real.exp (⟪cavityLeafSum n s v + z,
      Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s v + z)⟫ / 2))
      ∂multivariateGaussian 0 R ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V

lemma cavity_residual_lintegral {d : ℕ}
    (K R : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian) (hR : R.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt R)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    (∫⁻ z : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (Real.exp (⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + z)⟫ / 2))
        ∂multivariateGaussian 0 R) =
      ENNReal.ofReal (Real.exp (-Real.log (1 - R * K).det / 2 +
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K R) u⟫ / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (cavity_multivariate_gaussian_integrable K R hK hQ u)
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
    cavity_residual_integral K R hK hR hQ u]

lemma cavityResidualPartition_eq_leafIntegral {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hK : K.IsHermitian) (hH : (H n).PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    cavityResidualPartition n K (H n) s V =
      ∫⁻ v, ENNReal.ofReal (Real.exp (noiseLeafTerminal n
        (fun i z => cavityQuadraticValue n K H b i z - Real.log (1 - H n * K).det / 2)
          (fun _ p => p.1 + p.2) s v))
            ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V := by
  unfold cavityResidualPartition
  apply lintegral_congr
  intro v
  rw [cavity_residual_lintegral K (H n) hK hH hQ,
    cavity_noiseLeafTerminal_sum, cavityQuadraticValue_terminal]
  congr 2
  ring

lemma cavity_noiseTreeTotal_pos_finite {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
    ∀ᵐ V ∂(noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _),
      0 < noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V ∧
        noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V < ∞ := by
  apply ae_of_ae_map (μ := (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _))
    (p := fun V : RawTree n => 0 < rawTreeTotal n V ∧ rawTreeTotal n V < ∞)
    (measurable_noiseTreeForget (EuclideanSpace ℝ (Fin d)) n).aemeasurable
  rw [noiseCascadeLaw_forget]
  exact (rawCascade_total_moments n b hb).1

lemma cavity_residual_factor_log_eq {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (hK : K.IsHermitian) (hH : (H n).PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) :
    let X := fun i z => cavityQuadraticValue n K H b i z - Real.log (1 - H n * K).det / 2
    ∀ᵐ V ∂(noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _),
      Real.log ((noiseTreeFactor n b μ X (fun _ p => p.1 + p.2) s V).toReal /
        (noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V).toReal) =
        Real.log (cavityResidualPartition n K (H n) s V).toReal := by
  dsimp only
  let X := fun i z => cavityQuadraticValue n K H b i z - Real.log (1 - H n * K).det / 2
  have hX : ∀ i, Measurable (X i) := fun i =>
    (measurable_cavityQuadraticValue n K H b i).sub_const _
  have hu : ∀ i : ℕ, Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2) :=
    fun _ => measurable_fst.add measurable_snd
  filter_upwards [noiseTreeFactor_leafIntegral n b hb μ hX hu s,
    cavity_noiseTreeTotal_pos_finite n b hb μ] with V hV ht
  change Real.log ((noiseTreeFactor n b μ X _ s V).toReal / _) = _
  rw [hV, ← cavityResidualPartition_eq_leafIntegral n K H b hK hH hQ s V,
    ENNReal.toReal_mul]
  congr 1
  exact mul_div_cancel_left₀ _ (ENNReal.toReal_pos ht.1.ne' ht.2.ne).ne'


lemma measurable_cavityResidualPartition {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hK : K.IsHermitian) (hH : (H n).PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
      cavityResidualPartition n K (H n) p.1 p.2) := by
  have he : (fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
      cavityResidualPartition n K (H n) p.1 p.2) = fun p =>
        ∫⁻ v, ENNReal.ofReal (Real.exp (noiseLeafTerminal n
          (fun i z => cavityQuadraticValue n K H b i z - Real.log (1 - H n * K).det / 2)
            (fun _ q => q.1 + q.2) p.1 v))
              ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n p.2 := by
    funext p
    exact cavityResidualPartition_eq_leafIntegral n K H b hK hH hQ p.1 p.2
  rw [he]
  exact measurable_noiseLeafIntegral n
    (fun i => (measurable_cavityQuadraticValue n K H b i).sub_const _)
    (fun _ => measurable_fst.add measurable_snd)

/-- The complete source normalizer, including the last ordinary Gaussian
integral and the common Gaussian root, is logarithmically integrable. -/
theorem cavity_residual_partition_log_integral {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef) :
    let P := (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let Z := fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
      Real.log (cavityResidualPartition n K (H n) p.1 p.2).toReal
    Integrable Z ((multivariateGaussian 0 S₀).prod P) ∧
      (∫ p, Z p ∂(multivariateGaussian 0 S₀).prod P) =
        Matrix.trace (S₀ * cavityBackwardQuadratic K (H 0)) / 2 -
          (∑ j ∈ Finset.range n, cavityDeterminantStep K H b j) -
            Real.log (1 - H n * K).det / 2 := by
  dsimp only
  let μ := cavityGaussianMarks S
  let P : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n) := noiseCascadeLaw _ n b μ
  have : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let X := fun i z => cavityQuadraticValue n K H b i z - Real.log (1 - H n * K).det / 2
  let F := fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
    Real.log ((noiseTreeFactor n b μ X (fun _ q => q.1 + q.2) p.1 p.2).toReal /
      (noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n p.2).toReal)
  let Z := fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
    Real.log (cavityResidualPartition n K (H n) p.1 p.2).toReal
  have hX : ∀ i, Measurable (X i) := fun i =>
    (measurable_cavityQuadraticValue n K H b i).sub_const _
  have hF : Measurable F :=
    (((measurable_noiseTreeFactor n b μ hX (fun _ => measurable_fst.add measurable_snd)).ennreal_toReal).div
      (((measurable_noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n).comp measurable_snd).ennreal_toReal)).log
  have hKh : K.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hK
  have hZ : Measurable Z :=
    (measurable_cavityResidualPartition n K H b hKh hR hQR).ennreal_toReal.log
  have he : F =ᵐ[(multivariateGaussian 0 S₀).prod P] Z := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hF hZ)).mpr
    exact Filter.Eventually.of_forall (fun s =>
      cavity_residual_factor_log_eq n K H b hbCascade μ hKh hR hQR s)
  have hi := cavity_quadratic_root_log_integral_add_const n K H S b S₀ hS₀
    (-Real.log (1 - H n * K).det / 2) hbCascade hK hH hS hb hdet hΔ hQ
  dsimp only at hi
  have heX : (fun i z => cavityQuadraticValue n K H b i z +
      -Real.log (1 - H n * K).det / 2) = X := by
    funext i z
    dsimp only [X]
    ring
  rw [heX] at hi
  change Integrable F ((multivariateGaussian 0 S₀).prod P) ∧ _ at hi
  refine ⟨hi.1.congr he, ?_⟩
  rw [← integral_congr_ae he, hi.2]
  ring

end InvariantIsing

end

end OAI
