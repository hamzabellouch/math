import OAI.Probability.InvariantIsing.Cavity.CavitySpinIntegrability

namespace OAI

/-! The full cavity logarithmic normalizer splits into the quadratic
normalizer and the linear normalizer under the same innovation map. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal RealInnerProductSpace

namespace InvariantIsing

lemma cavity_log_integral_exp_add {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (Q F : E → ℝ)
    (hQ : Integrable (fun p => Real.exp (Q p)) μ)
    (hQF : Integrable (fun p => Real.exp (Q p + F p)) μ) :
    Real.log (∫ p, Real.exp (Q p + F p) ∂μ) =
      Real.log (∫ p, Real.exp (Q p) ∂μ) +
        Real.log (∫ p, Real.exp (F p) ∂μ.tilted Q) := by
  rw [integral_exp_tilted]
  simp only [Pi.add_apply]
  rw [Real.log_div (integral_exp_pos hQF).ne' (integral_exp_pos hQ).ne']
  ring

def cavityRootedLogNormalizer {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) : ℝ :=
  Real.log (∫ z, Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2)
    ∂(cavityRootedPriorKernel n R ω).prod π)

lemma measurable_cavityRootedLogNormalizer {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    Measurable (cavityRootedLogNormalizer n K R L C π) := by
  let κ := (cavityRootedPriorKernel n R).prod
    (Kernel.const (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) π)
  have hm := (((measurable_cavityRootedLogFactor n K L C).exp.comp
    measurable_snd).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable.log
  unfold cavityRootedLogNormalizer
  simpa only [κ, Kernel.prod_apply, Kernel.const_apply, Function.comp_def] using hm

lemma cavityRootedLogNormalizer_eq_residual {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    cavityRootedLogNormalizer n K R L C π (s, V) =
      Real.log (∫ p, Real.exp (cavityLogFactor K L C
        (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2)
          ∂((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
            (multivariateGaussian 0 R)).prod π) := by
  unfold cavityRootedLogNormalizer
  rw [cavityRootedPrior_spin_eq_map n R π s V,
    integral_map (measurable_cavityAttachSpinRoot n s).aemeasurable
      (measurable_cavityRootedLogFactor n K L C).exp.aestronglyMeasurable]
  rfl

lemma cavity_residual_partition_toReal {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R s V < ∞) :
    (cavityResidualPartition n K R s V).toReal =
      ∫ p, Real.exp (⟪cavityLeafSum n s p.1 + p.2,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2)
          ∂(noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
            (multivariateGaussian 0 R) := by
  have hi := cavity_residual_quadratic_integrable n K R s V hZ
  have hm : Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (Real.exp
        (⟪cavityLeafSum n s p.1 + p.2,
          Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2))) := by
    have hs := measurable_cavityLeafSum n s
    fun_prop
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun _ => (Real.exp_pos _).le))
  rw [lintegral_prod _ hm.aemeasurable] at he
  change ENNReal.ofReal _ = cavityResidualPartition n K R s V at he
  rw [← he, ENNReal.toReal_ofReal (integral_nonneg (fun _ => (Real.exp_pos _).le))]

theorem cavity_full_log_normalizer_transport {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hK : K.transpose = K) (hR : (H n).PosSemidef)
    (hdet : IsUnit (1 - H n * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K (H n) s V < ∞)
    (hV : NoiseGibbsRegular n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) s V)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (he : Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n (H n) (s, V)).prod π)) :
    let s' := Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s
    let V' := cavityInnovationTree n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun i => cavityStepInnovation K (H i) (H (i + 1))) s V
    cavityRootedLogNormalizer n K (H n) L C π (s, V) =
      Real.log (cavityResidualPartition n K (H n) s V).toReal +
        cavityRootedLogNormalizer n 0 (cavityResolvent K (H n)) L C π (s', V') := by
  intro s' V'
  let E := (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) × Spin k
  let μ := ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
    (multivariateGaussian 0 (H n))).prod π
  let Q := fun p : E => ⟪cavityLeafSum n s p.1.1 + p.1.2,
    Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1.1 + p.1.2)⟫ / 2
  let F := cavityLinearResidualPotential n L C s
  let T := Prod.map (cavityResidualInnovationMap n K H b s) (id : Spin k → Spin k)
  let η := ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V').prod
    (multivariateGaussian 0 (cavityResolvent K (H n)))).prod π
  have hT : Measurable T := (measurable_cavityResidualInnovationMap n K H b s).prodMap measurable_id
  have hQm : Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d) => ⟪cavityLeafSum n s p.1 + p.2,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2) := by
    have hs := measurable_cavityLeafSum n s
    fun_prop
  have hiQ := cavity_residual_quadratic_integrable n K (H n) s V hZ
  have hraw : Integrable (fun p : E => Real.exp (Q p + F p)) μ := by
    rw [cavityRootedPrior_spin_eq_map n (H n) π s V] at he
    have hi := (integrable_map_measure
      (measurable_cavityRootedLogFactor n K L C).exp.aestronglyMeasurable
      (measurable_cavityAttachSpinRoot n s).aemeasurable).mp he
    convert hi using 1
    funext p
    exact congrArg Real.exp (cavity_rooted_exponent_split n K L C ((s, p.1), p.2))
  have hq : μ.tilted Q = (cavityQuadraticResidualGibbs n K (H n) s V).prod π := by
    rw [cavityQuadraticResidualGibbs_eq_tilted n K (H n) s V hZ,
      cavity_tilt_prod_left _ π _ hQm]
  have hmap : (μ.tilted Q).map T = η := by
    rw [hq, show T = Prod.map (cavityResidualInnovationMap n K H b s) id from rfl,
      ← Measure.map_prod_map _ _ (measurable_cavityResidualInnovationMap n K H b s) measurable_id,
      Measure.map_id]
    have hlaw := cavity_residual_innovation_leaf_law n K H S b hK hR hdet hQ s V hZ hV
    change (cavityQuadraticResidualGibbs n K (H n) s V).map
      (cavityResidualInnovationMap n K H b s) = _ at hlaw
    rw [hlaw]
  have hlin : (∫ p, Real.exp (F p) ∂μ.tilted Q) =
      ∫ p, Real.exp (cavityLinearResidualPotential n L C s' p) ∂η := by
    rw [← hmap, integral_map hT.aemeasurable
      (measurable_cavityLinearResidualPotential n L C s').exp.aestronglyMeasurable]
    congr 1
    funext p
    dsimp only [F, T, Prod.map, id_eq, cavityLinearResidualPotential, s']
    rw [cavity_residual_innovation_sum]
  rw [cavityRootedLogNormalizer_eq_residual, cavityRootedLogNormalizer_eq_residual]
  have hsplit (p : E) : cavityLogFactor K L C
      (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2 = Q p + F p :=
    (cavity_rooted_exponent_split n K L C ((s, p.1), p.2)).symm
  simp_rw [hsplit]
  rw [cavity_log_integral_exp_add μ Q F (hiQ.comp_fst π) hraw, hlin]
  congr 1
  rw [integral_prod _ (hiQ.comp_fst π)]
  simp only [integral_const, probReal_univ, one_smul]
  exact congrArg Real.log (cavity_residual_partition_toReal n K (H n) s V hZ).symm

end InvariantIsing

end

end OAI
