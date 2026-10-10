import OAI.Probability.InvariantIsing.Magnetic.RestrictedTreeAverage

namespace OAI

/-! Measurability and boundedness of the fixed-tree physical restricted
mean needed to restore the random cascade prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem restricted_tree_regular {N m depth q d k r : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
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
    Measurable (fun V : LabeledTree depth =>
      ∫ p, cavityWeightedReplicaMean ((restrictedRotationProbability S hS eig I u p.1).prod π)
        (fun x => cavityHaarRestrictedWeight e (cavityRotationVectors dims E) A₀ K L C T B (p,x))
        F ∂(((μ.prod (Measure.dirac V)).prod gaussianCoordinates).prod η)) ∧
    ∀ V : LabeledTree depth,
      |∫ p, cavityWeightedReplicaMean ((restrictedRotationProbability S hS eig I u p.1).prod π)
        (fun x => cavityHaarRestrictedWeight e (cavityRotationVectors dims E) A₀ K L C T B (p,x))
        F ∂(((μ.prod (Measure.dirac V)).prod gaussianCoordinates).prod η)| ≤ M := by
  let ν := restrictedRotationProbability S hS (depth := depth) eig I u
  let w := cavityHaarRestrictedWeight e (cavityRotationVectors (depth := depth) dims E) A₀ K L C T B
  let κ := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (dims a))
    ν (measurable_restrictedRotationProbability S hS eig I u) π
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
  constructor
  · have hh := measurable_cavity_bounded_dirac_integral μ gaussianCoordinates η f hf hb
    simpa only [f,κ,cavityHaarSpinPriorKernel_apply,ν,w] using hh
  · intro V
    have hh := abs_integral_le_const_of_bound
      (μ := ((μ.prod (Measure.dirac V)).prod gaussianCoordinates).prod η) hf hb
    simpa only [f,κ,cavityHaarSpinPriorKernel_apply,ν,w] using hh

end InvariantIsing

end

end OAI
