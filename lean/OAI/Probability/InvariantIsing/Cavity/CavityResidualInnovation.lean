import OAI.Probability.InvariantIsing.Cavity.CavityResidualLeafLaw

namespace OAI

/-! The joint innovation map for a true cascade leaf and its ordinary
terminal residual. All residual randomness remains outside the cascade. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

def cavityQuadraticResidualGibbs {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    Measure (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) :=
  normalizeMass (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
    (multivariateGaussian 0 R)).withDensity
      (fun p => ENNReal.ofReal (Real.exp (⟪cavityLeafSum n s p.1 + p.2,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2))))

instance cavityQuadraticResidualGibbs_probability {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    IsProbabilityMeasure (cavityQuadraticResidualGibbs n K R s V) :=
  normalizeMass_probability _

lemma measurable_cavityQuadraticResidualGibbs {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d)) :
    Measurable (cavityQuadraticResidualGibbs n K R s) := by
  let G := (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n) ×ₖ
    Kernel.const (NoiseTree (EuclideanSpace ℝ (Fin d)) n) (multivariateGaussian 0 R)
  have hG : Measurable (fun V : NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
      (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod (multivariateGaussian 0 R)) := by
    have he : (fun V : NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
        (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod (multivariateGaussian 0 R)) = G := by
      funext V
      exact (Kernel.prod_apply (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n)
        (Kernel.const (NoiseTree (EuclideanSpace ℝ (Fin d)) n) (multivariateGaussian 0 R)) V).symm
    rw [he]
    exact G.measurable
  have hw : Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (Real.exp (⟪cavityLeafSum n s p.1 + p.2,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2))) := by
    have hs := measurable_cavityLeafSum n s
    fun_prop
  exact measurable_normalizeMass.comp ((measurable_withDensity_fixed hw).comp hG)

def cavityResidualInnovationMap {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (s : EuclideanSpace ℝ (Fin d))
    (p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) :
    NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d) :=
  (cavityInnovationLeaf n
    (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
    (fun i => cavityStepInnovation K (H i) (H (i + 1))) s p.1,
    cavityLeafSum n s p.1 + p.2 -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H n * K)⁻¹ (cavityLeafSum n s p.1))

lemma measurable_cavityResidualInnovationMap {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (s : EuclideanSpace ℝ (Fin d)) : Measurable (cavityResidualInnovationMap n K H b s) := by
  have hL : Measurable (cavityInnovationLeaf n
    (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
    (fun i => cavityStepInnovation K (H i) (H (i + 1))) s) :=
    (measurable_cavityInnovationLeaf n
    (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
    (fun i => cavityStepInnovation K (H i) (H (i + 1)))
    (fun i => measurable_cavityQuadraticStepWeight _ _ _ _)
    (fun i => measurable_cavityStepInnovation _ _ _)).comp
      (measurable_const.prodMk measurable_id)
  have hs := measurable_cavityLeafSum n s
  unfold cavityResidualInnovationMap
  exact (hL.comp measurable_fst).prodMk
    (((hs.comp measurable_fst).add measurable_snd).sub
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H n * K)⁻¹).measurable.comp
        (hs.comp measurable_fst)))

/-- At every regular tree the transformed leaf and centered terminal
residual are independent, with the leaf law of the innovation tree. -/
theorem cavity_residual_innovation_leaf_law {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hK : K.transpose = K) (hR : (H n).PosSemidef)
    (hdet : IsUnit (1 - H n * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K (H n) s V < ∞)
    (hV : NoiseGibbsRegular n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) s V) :
    (cavityQuadraticResidualGibbs n K (H n) s V).map
      (fun p => (cavityInnovationLeaf n
        (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
        (fun i => cavityStepInnovation K (H i) (H (i + 1))) s p.1,
        cavityLeafSum n s p.1 + p.2 -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H n * K)⁻¹ (cavityLeafSum n s p.1))) =
      (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n
        (cavityInnovationTree n b (cavityGaussianMarks S)
          (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
          (fun i => cavityStepInnovation K (H i) (H (i + 1))) s V)).prod
        (multivariateGaussian 0 (cavityResolvent K (H n))) := by
  let c := fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
  let g := fun i => cavityStepInnovation K (H i) (H (i + 1))
  let L := cavityInnovationLeaf n c g s
  let R := fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d) =>
    (p.1, cavityLeafSum n s p.1 + p.2 -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H n * K)⁻¹ (cavityLeafSum n s p.1))
  have hc : ∀ i, Measurable (c i) := fun i => measurable_cavityQuadraticStepWeight _ _ _ _
  have hg : ∀ i, Measurable (g i) := fun i => measurable_cavityStepInnovation _ _ _
  have hL : Measurable L := (measurable_cavityInnovationLeaf n c g hc hg).comp
    (measurable_const.prodMk measurable_id)
  have hRmap : Measurable R := by
    have hs := measurable_cavityLeafSum n s
    dsimp [R]
    fun_prop
  have he := cavity_quadratic_residual_leaf_law n K H b hK hR hdet hQ s V hZ
  change (cavityQuadraticResidualGibbs n K (H n) s V).map R = _ at he
  change (cavityQuadraticResidualGibbs n K (H n) s V).map ((Prod.map L id) ∘ R) = _
  rw [← Measure.map_map (hL.prodMap measurable_id) hRmap, he,
    ← Measure.map_prod_map _ _ hL measurable_id, Measure.map_id]
  rw [cavityInnovationLeaf_tilted_law n b (cavityGaussianMarks S) c g hc hg
    (fun i u a => cavityQuadraticStepWeight_pos _ _ _ _ (u, a)) s V hV]

end InvariantIsing

end

end OAI
