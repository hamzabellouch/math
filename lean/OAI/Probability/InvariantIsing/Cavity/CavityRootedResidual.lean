import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticOneReplica

namespace OAI

/-! The quadratic cavity kernel with the common root retained in its state. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal RealInnerProductSpace

namespace InvariantIsing

private def rootedResidualPrior {d : ℕ} (n : ℕ) (R : Matrix (Fin d) (Fin d) ℝ) :
    Kernel (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) :=
  ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n).comap Prod.snd measurable_snd) ×ₖ
    Kernel.const (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
      (multivariateGaussian 0 R)

private instance rootedResidualPrior_markov {d : ℕ} (n : ℕ)
    (R : Matrix (Fin d) (Fin d) ℝ) : IsMarkovKernel (rootedResidualPrior n R) := by
  unfold rootedResidualPrior
  infer_instance

private def rootedResidualWeight {d : ℕ} (n : ℕ) (K : Matrix (Fin d) (Fin d) ℝ)
    (p : (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (⟪cavityLeafSum n p.1.1 p.2.1 + p.2.2,
    Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n p.1.1 p.2.1 + p.2.2)⟫ / 2))

private lemma measurable_rootedResidualWeight {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) : Measurable (rootedResidualWeight n K) := by
  have hY : Measurable (fun p : (EuclideanSpace ℝ (Fin d) ×
      NoiseTree (EuclideanSpace ℝ (Fin d)) n) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) =>
      cavityLeafSum n p.1.1 p.2.1 + p.2.2) :=
    ((measurable_cavityLeafSum_joint n).comp
      (measurable_fst.fst.prodMk measurable_snd.fst)).add measurable_snd.snd
  exact ENNReal.measurable_ofReal.comp
    ((hY.inner ((Matrix.toEuclideanCLM (𝕜 := ℝ) K).measurable.comp hY)).div_const 2).exp

lemma measurable_cavityQuadraticResidualGibbs_joint {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
      cavityQuadraticResidualGibbs n K R p.1 p.2) := by
  have hm := measurable_normalizeMass.comp (measurable_random_withDensity
    (ν := rootedResidualPrior n R) (W := rootedResidualWeight n K)
    (rootedResidualPrior n R).measurable (measurable_rootedResidualWeight n K))
  convert hm using 1
  funext p
  unfold cavityQuadraticResidualGibbs rootedResidualWeight
  dsimp only [Function.comp_def]
  rw [rootedResidualPrior, Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply]

def cavityRootedResidualBaseKernel {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) :
    Kernel (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) :=
  ⟨fun p => cavityQuadraticResidualGibbs n K R p.1 p.2,
    measurable_cavityQuadraticResidualGibbs_joint n K R⟩

instance cavityRootedResidualBaseKernel_markov {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) :
    IsMarkovKernel (cavityRootedResidualBaseKernel n K R) := by
  constructor
  intro p
  change IsProbabilityMeasure (cavityQuadraticResidualGibbs n K R p.1 p.2)
  infer_instance

def cavityRootedResidualKernel {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) :
    Kernel (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
      (EuclideanSpace ℝ (Fin d) ×
        (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) :=
  Kernel.deterministic Prod.fst measurable_fst ×ₖ cavityRootedResidualBaseKernel n K R

instance cavityRootedResidualKernel_markov {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) :
    IsMarkovKernel (cavityRootedResidualKernel n K R) := by
  unfold cavityRootedResidualKernel
  infer_instance

def cavityRootedField {d : ℕ} (n : ℕ)
    (x : EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) := cavityLeafSum n x.1 x.2.1 + x.2.2

lemma measurable_cavityRootedField {d : ℕ} (n : ℕ) :
    Measurable (cavityRootedField (d := d) n) :=
  ((measurable_cavityLeafSum_joint n).comp
    (measurable_fst.prodMk measurable_snd.fst)).add measurable_snd.snd

lemma cavity_rooted_kernel_test {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ)
    (p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F (cavityRootedField n x) ∂cavityRootedResidualKernel n K R p) =
      ∫⁻ x, F (cavityLeafSum n p.1 x.1 + x.2) ∂cavityQuadraticResidualGibbs n K R p.1 p.2 := by
  rw [cavityRootedResidualKernel, Kernel.prod_apply, Kernel.deterministic_apply]
  rw [lintegral_prod _ (show AEMeasurable (fun x => F (cavityRootedField n x)) _ from
    (hF.comp (measurable_cavityRootedField n)).aemeasurable), lintegral_dirac]
  rfl

end InvariantIsing

end

end OAI
