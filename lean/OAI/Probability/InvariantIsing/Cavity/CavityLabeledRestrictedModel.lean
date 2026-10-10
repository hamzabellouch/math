import OAI.Probability.InvariantIsing.Cavity.CavityLabeledModelNumerator
import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedFactor

namespace OAI

/-! The actual finite labeled Gibbs numerator with its hard spatial
restriction and fixed logarithmic cap. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityLabeledRestrictedWeight {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ) :
    CavityLabeledDisorder d n × CavityLabeledState d k n → ℝ :=
  (fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
    cavityRestrictedFactor K L C T B p.1 p.2) ∘ cavityLabeledEndpoint n

lemma measurable_cavityLabeledRestrictedWeight {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ) :
    Measurable (cavityLabeledRestrictedWeight n K L C T B) :=
  (measurable_cavityRestrictedFactor K L C T B).comp (measurable_cavityLabeledEndpoint n)

lemma cavityLabeledRestrictedWeight_mem {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (p : CavityLabeledDisorder d n × CavityLabeledState d k n) :
    cavityLabeledRestrictedWeight n K L C T B p ∈ Set.Icc 0 (Real.exp T) :=
  cavityRestrictedFactor_mem K L C T B _ _

def cavityLabeledRestrictedNumerator {m r d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T Bcut : ℝ) (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) (ω : CavityLabeledDisorder d n) : ℝ :=
  cavityWeightNumerator (cavityLabeledPriorKernel n R π ω)
    (fun x => cavityLabeledRestrictedWeight n K L C T Bcut (ω,x))
    (fun ξ => cavityLabeledReplicaTest B F (ω,ξ))

lemma measurable_cavityLabeledRestrictedNumerator {m r d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T Bcut : ℝ) (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Measurable (cavityLabeledRestrictedNumerator n K R L C π T Bcut B F) :=
  measurable_cavityWeightNumerator (cavityLabeledPriorKernel n R π)
    (cavityLabeledPriorKernel n R π).measurable _
    (measurable_cavityLabeledRestrictedWeight n K L C T Bcut) _
    (measurable_cavityLabeledReplicaTest B F)

lemma cavityLabeledRestrictedNumerator_bound {m r d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T Bcut : ℝ) (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) (ω : CavityLabeledDisorder d n) :
    ‖cavityLabeledRestrictedNumerator n K R L C π T Bcut B F ω‖ ≤ ‖F‖*(Real.exp T)^r := by
  rw [Real.norm_eq_abs]
  apply cavityWeightNumerator_abs_le (cavityLabeledPriorKernel n R π ω) _ _
    (Real.exp_pos T).le (norm_nonneg F)
  · intro x
    rw [abs_of_nonneg (cavityLabeledRestrictedWeight_mem n K L C T Bcut (ω,x)).1]
    exact (cavityLabeledRestrictedWeight_mem n K L C T Bcut (ω,x)).2
  · intro ξ
    simpa only [cavityLabeledReplicaTest,Real.norm_eq_abs] using F.norm_coe_le_norm _

lemma cavityLabeledRestrictedNumerator_eq {m r d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T Bcut : ℝ) (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) (ω : CavityLabeledDisorder d n) :
    cavityLabeledRestrictedNumerator n K R L C π T Bcut B F ω =
      cavityWeightNumerator (((labeledLeafLaw n ω.1).prod (multivariateGaussian 0 R)).prod π)
        (fun p => cavityRestrictedFactor K L C T Bcut
          (cavityLeafSum n ω.2.1 (labeledNoiseLeaf _ n
            (ω.1,markForestOfCoords _ n ω.2.2) p.1.1)+p.1.2) p.2)
        (fun ξ => F (B (fun i => (ξ i).1.1),fun i => (ξ i).2)) := by
  simp only [cavityLabeledRestrictedNumerator,cavityLabeledPriorKernel_apply,
    cavityLabeledRestrictedWeight,Function.comp_apply,cavityLabeledEndpoint,
    cavityLabeledReplicaTest,cavityLabeledField,cavity_labeled_leaf_sum]

lemma integral_cavityLabeledRestrictedNumerator {m r d k : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] (τ Bcut : ℝ)
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    (∫ ω, cavityLabeledRestrictedNumerator n K R L C π τ Bcut B F ω
      ∂cavityLabeledDisorderLaw n b S₀ S) =
      ∫ T, ∫ sg, cavityWeightNumerator
        (((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod π)
        (fun p => cavityRestrictedFactor K L C τ Bcut
          (cavityLeafSum n sg.1 (labeledNoiseLeaf _ n
            (T, markForestOfCoords _ n sg.2) p.1.1) + p.1.2) p.2)
        (fun ξ => F (B (fun i => (ξ i).1.1), fun i => (ξ i).2))
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  have hi : Integrable (cavityLabeledRestrictedNumerator n K R L C π τ Bcut B F)
      (cavityLabeledDisorderLaw n b S₀ S) :=
    (integrable_const (‖F‖ * (Real.exp τ)^r)).mono'
      (measurable_cavityLabeledRestrictedNumerator n K R L C π τ Bcut B F).aestronglyMeasurable
      (ae_of_all _ (cavityLabeledRestrictedNumerator_bound n K R L C π τ Bcut B F))
  rw [cavityLabeledDisorderLaw, integral_prod _ hi]
  simp_rw [cavityLabeledRestrictedNumerator_eq]

end InvariantIsing

end

end OAI
