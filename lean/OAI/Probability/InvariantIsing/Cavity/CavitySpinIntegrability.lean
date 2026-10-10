import OAI.Probability.InvariantIsing.Cavity.CavityRootedSpinTransport

namespace OAI

/-! Transfer of the remaining spin exponential integrability through the
quadratic innovation law. No integrability of the transformed tilt is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal RealInnerProductSpace

namespace InvariantIsing

lemma cavityRootedPrior_spin_eq_map {d k : ℕ} (n : ℕ)
    (R : Matrix (Fin d) (Fin d) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    (cavityRootedPriorKernel n R (s, V)).prod π =
      ((((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod (multivariateGaussian 0 R)).prod π).map
        (cavityAttachSpinRoot n s)) := by
  rw [cavityRootedPriorKernel, Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply, Measure.dirac_prod]
  have hA : cavityAttachSpinRoot (k := k) n s = Prod.map (Prod.mk s) id := by
    funext p
    rfl
  rw [hA]
  simpa only [Measure.map_id] using Measure.map_prod_map
    ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod (multivariateGaussian 0 R)) π
    (show Measurable (Prod.mk s :
      NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d) →
        EuclideanSpace ℝ (Fin d) ×
          (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) from
            measurable_const.prodMk measurable_id) measurable_id

theorem cavity_spin_innovation_exp_integrable {d k : ℕ} (n : ℕ)
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
    Integrable (fun z => Real.exp (cavityLogFactor 0 L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n (cavityResolvent K (H n)) (s', V')).prod π) := by
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
  have hiQ : Integrable (fun p => Real.exp (Q p)) μ :=
    (cavity_residual_quadratic_integrable n K (H n) s V hZ).comp_fst π
  have hraw : Integrable (fun p : E => Real.exp (Q p + F p)) μ := by
    rw [cavityRootedPrior_spin_eq_map n (H n) π s V] at he
    have hi := (integrable_map_measure
      ((measurable_cavityRootedLogFactor n K L C).exp.aestronglyMeasurable)
      (measurable_cavityAttachSpinRoot n s).aemeasurable).mp he
    convert hi using 1
    funext p
    exact congrArg Real.exp (cavity_rooted_exponent_split n K L C ((s, p.1), p.2))
  have hq : (cavityQuadraticResidualGibbs n K (H n) s V).prod π = μ.tilted Q := by
    rw [cavityQuadraticResidualGibbs_eq_tilted n K (H n) s V hZ,
      cavity_tilt_prod_left _ π _ hQm]
  have hlin : Integrable (fun p => Real.exp (F p))
      ((cavityQuadraticResidualGibbs n K (H n) s V).prod π) := by
    rw [hq, integrable_tilted_iff hiQ]
    simpa only [smul_eq_mul, ← Real.exp_add] using hraw
  have hmap : ((cavityQuadraticResidualGibbs n K (H n) s V).prod π).map T = η := by
    rw [show T = Prod.map (cavityResidualInnovationMap n K H b s) id from rfl,
      ← Measure.map_prod_map _ _ (measurable_cavityResidualInnovationMap n K H b s) measurable_id,
      Measure.map_id]
    have hlaw := cavity_residual_innovation_leaf_law n K H S b hK hR hdet hQ s V hZ hV
    change (cavityQuadraticResidualGibbs n K (H n) s V).map
      (cavityResidualInnovationMap n K H b s) = _ at hlaw
    rw [hlaw]
  have hF : Measurable (cavityLinearResidualPotential n L C s') :=
    measurable_cavityLinearResidualPotential n L C s'
  have hpull : (fun p => Real.exp (cavityLinearResidualPotential n L C s' (T p))) =
      fun p => Real.exp (F p) := by
    funext p
    dsimp only [F, T, Prod.map, id_eq, cavityLinearResidualPotential, s']
    rw [cavity_residual_innovation_sum]
  have hi : Integrable (fun p => Real.exp (cavityLinearResidualPotential n L C s' p)) η := by
    rw [← hmap]
    apply (integrable_map_measure hF.exp.aestronglyMeasurable hT.aemeasurable).mpr
    change Integrable (fun p => Real.exp (cavityLinearResidualPotential n L C s' (T p))) _
    rwa [hpull]
  rw [cavityRootedPrior_spin_eq_map n (cavityResolvent K (H n)) π s' V']
  exact (integrable_map_measure
    ((measurable_cavityRootedLogFactor n 0 L C).exp.aestronglyMeasurable)
    (measurable_cavityAttachSpinRoot n s').aemeasurable).mpr hi

end InvariantIsing

end

end OAI
