import OAI.Probability.InvariantIsing.Cavity.CavityDiracAverage
import OAI.Probability.InvariantIsing.Cavity.CavityRotationRestrictedIntegral

namespace OAI

/-! Averaging fixed-tree restricted Gibbs means gives exactly the
physical product-disorder mean with its original random tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_restricted_tree_average {N m depth q d k r : ℕ}
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ]
    (dims : Fin m → ℕ) (E : ((a : Fin m) × Fin (dims a)) ≃ Fin N)
    (η : Measure ((a : Fin m) → Orthogonal (dims a))) [IsProbabilityMeasure η]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (e : Fin d → Fin m × Fin q)
    (A₀ : (a : Fin m) → Matrix (Fin (dims a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T B : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (F : (Fin r → (Spin N × LabeledLeaf depth) × Spin k) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    (∫ V, ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability eig I u p.1).prod π)
      (fun x => cavityHaarRestrictedWeight e (cavityRotationVectors dims E) A₀ K L C T B (p,x))
      F ∂(((μ.prod (Measure.dirac V)).prod gaussianCoordinates).prod η) ∂θ) =
    ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability eig I u p.1).prod π)
      (fun x => cavityHaarRestrictedWeight e (cavityRotationVectors dims E) A₀ K L C T B (p,x))
      F ∂(((μ.prod θ).prod gaussianCoordinates).prod η) := by
  let ν := cavityRotationProbability (depth := depth) eig I u
  let w := cavityHaarRestrictedWeight e (cavityRotationVectors (depth := depth) dims E) A₀ K L C T B
  let κ := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (dims a))
    ν (measurable_cavityRotationProbability eig I u) π
  let f := fun p => cavityWeightedReplicaMean (κ p) (fun x => w (p,x)) F
  have hw : Measurable w := measurable_cavityHaarRestrictedWeight e
    (cavityRotationVectors dims E) (measurable_cavityRotationVectors dims E) A₀ K L C T B
  have hf : Measurable f := by
    have hh := measurable_cavityRegularizedReplicaMean (fun p => κ p) κ.measurable
      w hw (fun p => F p.2) ((measurable_of_countable F).comp measurable_snd) 0
    simpa only [f,cavityRegularizedReplicaMean,add_zero,cavityWeightedReplicaMean] using hh
  have hb p : |f p| ≤ M := by
    have hh := cavityRegularizedReplicaMean_abs_le (κ p) (fun x => w (p,x))
      (hw.comp measurable_prodMk_left) F (measurable_of_countable F)
      (Real.exp_pos T).le hM (δ := 0) le_rfl
      (fun x => cavityHaarRestrictedWeight_mem e (cavityRotationVectors dims E) A₀ K L C T B (p,x)) hF
    simpa only [f,cavityRegularizedReplicaMean,add_zero,cavityWeightedReplicaMean] using hh
  have hh := cavity_bounded_dirac_average μ θ gaussianCoordinates η f hf hb
  simpa only [f,κ,cavityHaarSpinPriorKernel_apply,ν,w] using hh

end InvariantIsing

end

end OAI
