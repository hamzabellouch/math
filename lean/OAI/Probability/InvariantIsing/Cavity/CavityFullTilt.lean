import OAI.Probability.InvariantIsing.Cavity.CavitySpinLinearMoment
import OAI.Probability.InvariantIsing.Cavity.CavityTiltTransport

namespace OAI

/-! Identifying the two successive tilts with the full cavity factor on
the original leaf/residual/spin prior, with the common root retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityRootedPriorKernel {d : ℕ} (n : ℕ) (R : Matrix (Fin d) (Fin d) ℝ) :
    Kernel (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
      (EuclideanSpace ℝ (Fin d) ×
        (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) :=
  Kernel.deterministic Prod.fst measurable_fst ×ₖ
    (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n).comap Prod.snd measurable_snd) ×ₖ
      Kernel.const _ (multivariateGaussian 0 R))

instance cavityRootedPriorKernel_markov {d : ℕ} (n : ℕ)
    (R : Matrix (Fin d) (Fin d) ℝ) : IsMarkovKernel (cavityRootedPriorKernel n R) := by
  unfold cavityRootedPriorKernel
  infer_instance

def cavityRootedQuadratic {d : ℕ} (n : ℕ) (K : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) : ℝ :=
  ⟪cavityRootedField n x, Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityRootedField n x)⟫ / 2

lemma measurable_cavityRootedQuadratic {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) : Measurable (cavityRootedQuadratic n K) :=
  ((measurable_cavityRootedField n).inner
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) K).measurable.comp (measurable_cavityRootedField n))).div_const 2

lemma measurable_cavityRootedLogFactor {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) :
    Measurable (fun z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k =>
      cavityLogFactor K L C (cavityRootedField n z.1) z.2) := by
  have hy : ∀ i, Measurable (fun z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k =>
      cavityRootedField n z.1 i) := fun i =>
    (EuclideanSpace.proj i).measurable.comp ((measurable_cavityRootedField n).comp measurable_fst)
  have he : ∀ i, Measurable (fun z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k =>
      spinValue (z.2 i)) := by
    intro i
    exact (measurable_of_countable (spinValue : Bool → ℝ)).comp
      ((measurable_pi_apply i).comp measurable_snd)
  have hK : Measurable (fun z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k =>
      cavityQuadratic K (cavityRootedField n z.1)) := by
    exact (Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
      (fun j _ => ((hy i).mul_const (K i j)).mul (hy j)))).const_mul (1 / 2)
  have hL : Measurable (fun z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k =>
      ∑ i, ∑ j, cavityRootedField n z.1 i * L i j * spinValue (z.2 j)) :=
    Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
      (fun j _ => ((hy i).mul_const (L i j)).mul (he j)))
  have hC : Measurable (fun z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k =>
      cavityQuadratic C (fun i => spinValue (z.2 i))) := by
    exact (Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
      (fun j _ => ((he i).mul_const (C i j)).mul (he j)))).const_mul (1 / 2)
  exact (hK.add hL).add hC

lemma cavity_residual_quadratic_integrable {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R s V < ∞) :
    Integrable (fun z => Real.exp (⟪cavityLeafSum n s z.1 + z.2,
      Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s z.1 + z.2)⟫ / 2))
      ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod (multivariateGaussian 0 R)) := by
  have hm : Measurable (fun z : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d) => Real.exp (⟪cavityLeafSum n s z.1 + z.2,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s z.1 + z.2)⟫ / 2)) := by
    exact ((measurable_cavityRootedQuadratic n K).comp
      (measurable_const.prodMk measurable_id)).exp
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp only [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)]
  rw [lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
  exact hZ

theorem cavity_rooted_quadratic_eq_tilted {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ)
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R ω.1 ω.2 < ∞) :
    cavityRootedResidualKernel n K R ω =
      (cavityRootedPriorKernel n R ω).tilted (cavityRootedQuadratic n K) := by
  let μ := (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n ω.2).prod
    (multivariateGaussian 0 R)
  let F := fun z : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d) => (ω.1, z)
  let Q := cavityRootedQuadratic n K
  have hQ := measurable_cavityRootedQuadratic n K
  have hi := cavity_residual_quadratic_integrable n K R ω.1 ω.2 hZ
  have hg : cavityQuadraticResidualGibbs n K R ω.1 ω.2 = μ.tilted (Q ∘ F) := by
    unfold cavityQuadraticResidualGibbs
    exact normalizeMass_exp μ (Q ∘ F) (hQ.comp (measurable_const.prodMk measurable_id)) hi
  rw [cavityRootedResidualKernel, Kernel.prod_apply, Kernel.deterministic_apply]
  change (Measure.dirac ω.1).prod (cavityQuadraticResidualGibbs n K R ω.1 ω.2) = _
  rw [hg, Measure.dirac_prod]
  have hp : cavityRootedPriorKernel n R ω = μ.map F := by
    rw [cavityRootedPriorKernel, Kernel.prod_apply, Kernel.deterministic_apply,
      Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply, Measure.dirac_prod]
  rw [hp]
  exact cavity_tilt_map μ F (measurable_const.prodMk measurable_id) Q hQ

lemma cavity_tilt_prod_left {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (f : X → ℝ) (hf : Measurable f) :
    (μ.tilted f).prod ν = (μ.prod ν).tilted (fun z => f z.1) := by
  have he : (∫ z : X × Y, Real.exp (f z.1) ∂μ.prod ν) = ∫ x, Real.exp (f x) ∂μ := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_fst (μ := μ) (ν := ν) (fun x => Real.exp (f x)))
  rw [Measure.tilted, Measure.tilted,
    prod_withDensity_left (hf.exp.div_const _).ennreal_ofReal,
    he]

lemma cavityQuadratic_eq_inner {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    cavityQuadratic K y = ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) K y⟫ / 2 := by
  have hs : (∑ i, ∑ j, y i * K i j * y j) =
      ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) K y⟫ := by
    rw [Matrix.inner_toEuclideanCLM]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [cavityQuadratic, hs]
  ring

lemma cavity_rooted_exponent_split {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ)
    (z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k) :
    cavityRootedQuadratic n K z.1 + cavityLogFactor 0 L C (cavityRootedField n z.1) z.2 =
      cavityLogFactor K L C (cavityRootedField n z.1) z.2 := by
  have hz : cavityQuadratic (0 : Matrix (Fin d) (Fin d) ℝ) (cavityRootedField n z.1) = 0 := by
    simp [cavityQuadratic]
  dsimp only [cavityLogFactor, cavityRootedQuadratic]
  rw [hz, cavityQuadratic_eq_inner K (cavityRootedField n z.1)]
  ring

lemma cavity_rooted_quadratic_integrable {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ)
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R ω.1 ω.2 < ∞) :
    Integrable (fun z => Real.exp (cavityRootedQuadratic n K z))
      (cavityRootedPriorKernel n R ω) := by
  have hraw := cavity_residual_quadratic_integrable n K R ω.1 ω.2 hZ
  have hp : cavityRootedPriorKernel n R ω =
      ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n ω.2).prod
        (multivariateGaussian 0 R)).map (fun z => (ω.1, z)) := by
    rw [cavityRootedPriorKernel, Kernel.prod_apply, Kernel.deterministic_apply,
      Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply, Measure.dirac_prod]
  rw [hp]
  exact (integrable_map_measure ((measurable_cavityRootedQuadratic n K).exp.aestronglyMeasurable)
    (measurable_const.prodMk measurable_id).aemeasurable).mpr hraw

theorem cavity_rooted_full_tilt_eq {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R ω.1 ω.2 < ∞) :
    ((cavityRootedResidualKernel n K R ω).prod π).tilted
        (fun z => cavityLogFactor 0 L C (cavityRootedField n z.1) z.2) =
      ((cavityRootedPriorKernel n R ω).prod π).tilted
        (fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2) := by
  let μ := cavityRootedPriorKernel n R ω
  let Q := fun z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k =>
    cavityRootedQuadratic n K z.1
  have hi : Integrable (fun z => Real.exp (Q z)) (μ.prod π) := by
    exact (cavity_rooted_quadratic_integrable n K R ω hZ).comp_fst π
  rw [cavity_rooted_quadratic_eq_tilted n K R ω hZ,
    cavity_tilt_prod_left _ π _ (measurable_cavityRootedQuadratic n K), tilted_tilted hi]
  congr 1
  funext z
  change cavityRootedQuadratic n K z.1 +
    cavityLogFactor 0 L C (cavityRootedField n z.1) z.2 = _
  exact cavity_rooted_exponent_split n K L C z

theorem cavity_rooted_full_exp_integrable {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R ω.1 ω.2 < ∞)
    (hlin : Integrable (fun z => Real.exp (cavityLogFactor 0 L C (cavityRootedField n z.1) z.2))
      ((cavityRootedResidualKernel n K R ω).prod π)) :
    Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n R ω).prod π) := by
  rw [cavity_rooted_quadratic_eq_tilted n K R ω hZ,
    cavity_tilt_prod_left _ π _ (measurable_cavityRootedQuadratic n K)] at hlin
  have hi := (integrable_tilted_iff
    ((cavity_rooted_quadratic_integrable n K R ω hZ).comp_fst π) _).mp hlin
  have he := fun z => congrArg Real.exp (cavity_rooted_exponent_split n K L C z)
  simp only [Real.exp_add] at he
  simpa only [smul_eq_mul, he] using hi

end InvariantIsing

end

end OAI
