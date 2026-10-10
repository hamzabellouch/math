import OAI.Probability.InvariantIsing.Cavity.CavitySpinFullLaw
import OAI.Probability.InvariantIsing.Cavity.CavityFullGibbs
import OAI.Probability.InvariantIsing.Cavity.CavityRootInnovationLaw

namespace OAI

/-! Root-retaining transport of the full cavity spin probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

abbrev CavitySpinState (d k n : ℕ) :=
  (EuclideanSpace ℝ (Fin d) ×
    (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k

def cavityAttachSpinRoot {d k : ℕ} (n : ℕ) (s : EuclideanSpace ℝ (Fin d))
    (p : (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) × Spin k) :
    CavitySpinState d k n := ((s, p.1), p.2)

lemma measurable_cavityAttachSpinRoot {d k : ℕ} (n : ℕ) (s : EuclideanSpace ℝ (Fin d)) :
    Measurable (cavityAttachSpinRoot (k := k) n s) := by
  exact (measurable_const.prodMk measurable_fst).prodMk measurable_snd

lemma cavityRootedFullGibbs_eq_residual_map {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (he : Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n R (s, V)).prod π)) :
    cavityRootedFullGibbs n K R L C π (s, V) =
      (cavityResidualSpinFullLaw n K R L C s V π).map (cavityAttachSpinRoot n s) := by
  rw [cavityRootedFullGibbs_eq_tilted n K R L C π (s, V) he]
  let μ := ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
    (multivariateGaussian 0 R)).prod π
  let A := cavityAttachSpinRoot (k := k) n s
  let F := fun z : CavitySpinState d k n => cavityLogFactor K L C (cavityRootedField n z.1) z.2
  have hp : (cavityRootedPriorKernel n R (s, V)).prod π = μ.map A := by
    rw [cavityRootedPriorKernel, Kernel.prod_apply, Kernel.deterministic_apply,
      Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply, Measure.dirac_prod]
    have hA : A = Prod.map (Prod.mk s) (id : Spin k → Spin k) := by
      funext p
      rfl
    rw [hA]
    simpa only [Measure.map_id, μ] using Measure.map_prod_map
      ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod (multivariateGaussian 0 R)) π
      (show Measurable (Prod.mk s :
        NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) ×
            (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) from
              measurable_const.prodMk measurable_id) measurable_id
  rw [hp]
  change (μ.map A).tilted F = (μ.tilted (F ∘ A)).map A
  exact (cavity_tilt_map μ A (measurable_cavityAttachSpinRoot n s)
    F (measurable_cavityRootedLogFactor n K L C)).symm

def cavityRootedSpinInnovation {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) (p : CavitySpinState d k n) : CavitySpinState d k n :=
  ((Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ p.1.1,
    cavityResidualInnovationMap n K H b p.1.1 p.1.2), p.2)

lemma measurable_cavityRootedSpinInnovation {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) : Measurable (cavityRootedSpinInnovation (k := k) n K H b) := by
  unfold cavityRootedSpinInnovation cavityResidualInnovationMap
  have hm := measurable_cavityInnovationLeaf n
    (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
    (fun i => cavityStepInnovation K (H i) (H (i + 1)))
    (fun i => measurable_cavityQuadraticStepWeight _ _ _ _)
    (fun i => measurable_cavityStepInnovation _ _ _)
  have hs := measurable_cavityLeafSum_joint (d := d) n
  fun_prop

end InvariantIsing

end

end OAI
