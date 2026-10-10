import OAI.Probability.InvariantIsing.Cavity.CavityRootedSpinChange

namespace OAI

/-! Countably many full cavity replicas under the rooted innovation change. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal BigOperators

namespace InvariantIsing

lemma cavity_quadratic_regular_ae {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) :
    ∀ᵐ V ∂(noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _),
      NoiseGibbsRegular n b (cavityGaussianMarks S)
        (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
        (fun _ p => p.1 + p.2) s V := by
  have hc := fun i => measurable_cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
  have hu : ∀ _i : ℕ, Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2) :=
    fun _ => measurable_fst.add measurable_snd
  apply noiseGibbsRegular_ae n b hbCascade (cavityGaussianMarks S) hc hu
    (fun i x a => cavityQuadraticStepWeight_pos _ _ _ _ (x, a))
  intro i x
  have hv := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin d)) => μ Set.univ)
    (cavity_quadratic_step_weight_innovation_law K (H i) (H (i + 1)) (S i)
      hK (hH (i + 1)) (hS i) (b i) (hb i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i) x)
  have hg : Measurable (fun a : EuclideanSpace ℝ (Fin d) =>
      cavityStepInnovation K (H i) (H (i + 1)) (x, a)) :=
    (measurable_cavityStepInnovation K (H i) (H (i + 1))).comp
      (measurable_const.prodMk measurable_id)
  dsimp only [cavityStepInnovation] at hg
  rw [Measure.map_apply hg MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, measure_univ] at hv
  exact hv

lemma cavity_rooted_full_integrability {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    ∀ᵐ ω ∂P, cavityResidualPartition n K (H n) ω.1 ω.2 < ∞ ∧
      Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
        ((cavityRootedPriorKernel n (H n) ω).prod π) := by
  intro P
  let J₀ := (1 - H 0 * K)⁻¹
  have hZ : ∀ᵐ ω ∂P, cavityResidualPartition n K (H n) ω.1 ω.2 < ∞ := by
    have hm := measurable_cavityResidualPartition n K H b
      (Matrix.isHermitian_iff_isSymm.mpr hK) hR hQR
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hm measurable_const)).mpr
    exact Filter.Eventually.of_forall (fun s =>
      (cavity_residual_partition_pos_finite n K H S b hbCascade hK hH hS hb hdet hΔ hQ
        hR hQR s).mono (fun _ h => h.2))
  let T := J₀ * S₀ * J₀.transpose +
    ((∑ i : Fin n, (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) +
      cavityResolvent K (H n))
  have hT : T.PosSemidef := by
    have hroot : (J₀ * S₀ * J₀.transpose).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hS₀.mul_mul_conjTranspose_same J₀
    exact hroot.add ((Matrix.posSemidef_sum Finset.univ (fun (i : Fin n) _ =>
      cavity_innovation_covariance_posSemidef K (H i) (H (i + 1)) (S i) (hS i)
        (b i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i))).add
          (cavity_tilt_covariance_posSemidef K (H n) hR hQR))
  have hLaw : (cavityRootedResidualKernel n K (H n) ∘ₘ P).map (cavityRootedField n) =
      multivariateGaussian 0 T :=
    cavity_rooted_quadratic_gaussian n K H S b S₀ hS₀ hbCascade hK hH hS hb hdet hΔ hQ hR hQR
  have hlin := cavity_spin_linear_tilt_gaussian_moment P (cavityRootedResidualKernel n K (H n))
    (cavityRootedField n) (measurable_cavityRootedField n) π T hT hLaw L C (le_refl ‖T‖) 0
  have hfull : ∀ᵐ ω ∂P,
      Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
        ((cavityRootedPriorKernel n (H n) ω).prod π) := by
    filter_upwards [hZ, hlin.1] with ω hωZ hωlin
    apply cavity_rooted_full_exp_integrable n K (H n) L C π ω hωZ
    simpa only [Kernel.prod_apply, Kernel.const_apply] using hωlin.1
  filter_upwards [hZ, hfull] with ω hωZ hωfull
  exact ⟨hωZ, hωfull⟩

theorem cavity_rooted_full_replica_transport {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let J₀ := (1 - H 0 * K)⁻¹
    let P' := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (J₀ * S₀ * J₀.transpose)).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b
        (cavityGaussianMarks (fun i =>
          (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)) : Measure _)
    ((probabilityReplicaKernel (cavityRootedFullGibbs n K (H n) L C π)
      (cavityRootedFullGibbs n K (H n) L C π).measurable) ∘ₘ P).map
        (fun σ i => cavityRootedSpinInnovation n K H b (σ i)) =
      (probabilityReplicaKernel (cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π)
        (cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π).measurable) ∘ₘ P' := by
  intro P J₀ P'
  have hPQ : P.map (cavitySpinDisorderInnovation n K H S b) = P' :=
    cavity_quadratic_root_tree_law n K H S b S₀ hS₀ hK hH hS hb hdet hΔ hQ
  have hdata := cavity_rooted_full_integrability n K H S b S₀ hS₀ L C hbCascade
    hK hH hS hb hdet hΔ hQ hR hQR π
  apply cavity_replica_kernel_transport P P'
    (cavityRootedFullGibbs n K (H n) L C π).measurable
    (cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π).measurable
    (measurable_cavitySpinDisorderInnovation n K H S b) hPQ
    (measurable_cavityRootedSpinInnovation n K H b)
  have hc := fun i => measurable_cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
  have hu : ∀ _i : ℕ, Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2) :=
    fun _ => measurable_fst.add measurable_snd
  have hreg : ∀ᵐ ω ∂P, NoiseGibbsRegular n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) ω.1 ω.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_noiseGibbsRegular n b (cavityGaussianMarks S) hc hu)).mpr
    exact Filter.Eventually.of_forall (fun s =>
      cavity_quadratic_regular_ae n K H S b hbCascade hK hH hS hb hdet hΔ hQ s)
  filter_upwards [hdata, hreg] with ω hωdata hωreg
  exact cavity_rooted_full_spin_transport n K H S b L C hK hR (hdet n) hQR
    ω hωdata.1 hωreg π hωdata.2

end InvariantIsing

end

end OAI
