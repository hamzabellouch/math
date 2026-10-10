import OAI.Probability.InvariantIsing.Cavity.CavityLabeledModel

namespace OAI

/-! Measurability and the literal product-prior formula for the finite
cavity numerator used in extra-replica normalization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityLabeledReplicaTest {m r d k n : ℕ}
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (p : CavityLabeledDisorder d n × (Fin r → CavityLabeledState d k n)) : ℝ :=
  F (B (fun i => (p.2 i).1.1), fun i => (p.2 i).2)

lemma measurable_cavityLabeledReplicaTest {m r d k n : ℕ}
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Measurable (cavityLabeledReplicaTest (d := d) B F) := by
  have hl : Measurable (fun p : CavityLabeledDisorder d n × (Fin r → CavityLabeledState d k n) =>
      fun i => (p.2 i).1.1) :=
    Measurable.of_eval fun i => ((measurable_pi_apply i).comp measurable_snd).fst.fst
  have hs : Measurable (fun p : CavityLabeledDisorder d n × (Fin r → CavityLabeledState d k n) =>
      fun i => (p.2 i).2) :=
    Measurable.of_eval fun i => ((measurable_pi_apply i).comp measurable_snd).snd
  exact F.continuous.measurable.comp (((measurable_of_countable B).comp hl).prodMk hs)

def cavityLabeledCappedNumerator {m r d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] (τ : ℝ)
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) (ω : CavityLabeledDisorder d n) : ℝ :=
  cavityWeightNumerator (cavityLabeledPriorKernel n R π ω)
    (fun x => Real.exp (min (cavityLabeledPotential n K L C (ω, x)) τ))
    (fun ξ => cavityLabeledReplicaTest B F (ω, ξ))

lemma measurable_cavityLabeledCappedNumerator {m r d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] (τ : ℝ)
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Measurable (cavityLabeledCappedNumerator n K R L C π τ B F) :=
  measurable_cavityWeightNumerator (cavityLabeledPriorKernel n R π)
    (cavityLabeledPriorKernel n R π).measurable _
    (((measurable_cavityLabeledPotential n K L C).min measurable_const).exp) _
    (measurable_cavityLabeledReplicaTest B F)

lemma cavityLabeledCappedNumerator_bound {m r d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] (τ : ℝ)
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) (ω : CavityLabeledDisorder d n) :
    ‖cavityLabeledCappedNumerator n K R L C π τ B F ω‖ ≤ ‖F‖ * (Real.exp τ)^r := by
  rw [Real.norm_eq_abs]
  exact cavityWeightNumerator_abs_le (cavityLabeledPriorKernel n R π ω) _ _
    (Real.exp_pos τ).le (norm_nonneg F)
    (fun _ => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (min_le_right _ _))
    (fun ξ => by simpa only [cavityLabeledReplicaTest, Real.norm_eq_abs] using
      (F.norm_coe_le_norm (B (fun i => (ξ i).1.1), fun i => (ξ i).2)))

lemma cavityLabeledCappedNumerator_eq {m r d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] (τ : ℝ)
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) (ω : CavityLabeledDisorder d n) :
    cavityLabeledCappedNumerator n K R L C π τ B F ω =
      cavityWeightNumerator (((labeledLeafLaw n ω.1).prod (multivariateGaussian 0 R)).prod π)
        (fun p => Real.exp (min (cavityLogFactor K L C
          (cavityLeafSum n ω.2.1 (labeledNoiseLeaf _ n
            (ω.1, markForestOfCoords _ n ω.2.2) p.1.1) + p.1.2) p.2) τ))
        (fun ξ => F (B (fun i => (ξ i).1.1), fun i => (ξ i).2)) := by
  simp only [cavityLabeledCappedNumerator, cavityLabeledPriorKernel_apply,
    cavityLabeledPotential, Function.comp_apply, cavityLabeledEndpoint,
    cavityLabeledReplicaTest, cavityLabeledField,
    cavity_labeled_leaf_sum, WithLp.ofLp_add]

lemma integral_cavityLabeledCappedNumerator {m r d k : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] (τ : ℝ)
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    (∫ ω, cavityLabeledCappedNumerator n K R L C π τ B F ω
      ∂cavityLabeledDisorderLaw n b S₀ S) =
      ∫ T, ∫ sg, cavityWeightNumerator
        (((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod π)
        (fun p => Real.exp (min (cavityLogFactor K L C
          (cavityLeafSum n sg.1 (labeledNoiseLeaf _ n
            (T, markForestOfCoords _ n sg.2) p.1.1) + p.1.2) p.2) τ))
        (fun ξ => F (B (fun i => (ξ i).1.1), fun i => (ξ i).2))
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  have hi : Integrable (cavityLabeledCappedNumerator n K R L C π τ B F)
      (cavityLabeledDisorderLaw n b S₀ S) :=
    (integrable_const (‖F‖ * (Real.exp τ)^r)).mono'
      (measurable_cavityLabeledCappedNumerator n K R L C π τ B F).aestronglyMeasurable
      (ae_of_all _ (cavityLabeledCappedNumerator_bound n K R L C π τ B F))
  rw [cavityLabeledDisorderLaw, integral_prod _ hi]
  simp_rw [cavityLabeledCappedNumerator_eq]

end InvariantIsing

end

end OAI
