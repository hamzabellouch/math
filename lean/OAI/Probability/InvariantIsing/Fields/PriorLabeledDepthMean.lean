import OAI.Probability.InvariantIsing.Fields.PriorLabeledDepthPair
import OAI.Probability.InvariantIsing.Cavity.CavityRootedDepthMean
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledModelSpinMean

namespace OAI

/-! The finite labeled common-depth mean and its full rooted law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal BigOperators

namespace InvariantIsing

def priorCavityLabeledDepthMean {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] (a : ℕ → ℝ)
    (ω : CavityLabeledDisorder d n) : ℝ :=
  referenceReplicaMean (cavityLabeledPriorKernel n R π ω)
    (fun x => cavityLabeledPotential n K L C (ω,x))
    (fun σ : Fin 2 → CavityLabeledState d k n => a (labeledCommonDepth n (σ 0).1.1 (σ 1).1.1))

lemma prior_cavity_labeled_model_depth_mean {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] (a : ℕ → ℝ)
    (ω : CavityLabeledDisorder d n) (hgi : Function.Injective ω.2.2)
    (hg : GoodNoiseTree _ n (cavityLabeledNoiseDisorderMap n ω).2)
    (ht : 0 < noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 ∧
      noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 < ∞)
    (hI : Integrable (fun z => Real.exp
      (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n R (cavityLabeledNoiseDisorderMap n ω)).prod
        π)) :
    priorCavityLabeledDepthMean n K R L C π a ω =
      cavityRootedDepthTestMean n K R L C π a
        (cavityLabeledNoiseDisorderMap n ω) := by
  have hi := cavity_labeled_model_exp_integrable n K R L C π ω hg ht hI
  have hiraw : Integrable (fun p : CavityLabeledState d k n => Real.exp
      (cavityLogFactor K L C
        (cavityLeafSum n ω.2.1 (labeledNoiseLeaf _ n
          (ω.1, markForestOfCoords _ n ω.2.2) p.1.1) + p.1.2) p.2))
      (((labeledLeafLaw n ω.1).prod (multivariateGaussian 0 R)).prod π) := by
    simpa only [cavityLabeledPriorKernel_apply, cavityLabeledPotential, Function.comp_apply,
      cavityLabeledEndpoint, cavityLabeledField, cavity_labeled_leaf_sum, WithLp.ofLp_add] using hi
  have he := prior_cavity_labeled_rooted_depth_pair n K R L C π ω.2.1 ω.1 ω.2.2 hgi hg ht hiraw a
  simpa only [priorCavityLabeledDepthMean, cavityLabeledPriorKernel_apply,
    cavityLabeledPotential, Function.comp_apply, cavityLabeledEndpoint, cavityLabeledField,
    cavity_labeled_leaf_sum, WithLp.ofLp_add, cavityRootedDepthTestMean,
    cavityLabeledNoiseDisorderMap] using he.symm

theorem integral_priorCavityLabeledDepthMean {d k : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (K R S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (hb : CascadeExponents n b)
    (hAtom : ∀ i < n,
      NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i)))
    (hI : ∀ᵐ ω ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _),
      Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
        ((cavityRootedPriorKernel n R ω).prod π))
    (a : ℕ → ℝ) :
    (∫ ω, priorCavityLabeledDepthMean n K R L C π a ω ∂cavityLabeledDisorderLaw n b S₀ S) =
      ∫ ω, cavityRootedDepthTestMean n K R L C π a ω
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
          (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _) := by
  have hi := (cavity_labeled_noise_disorder_law n b S₀ S).quasiMeasurePreserving.ae hI
  calc
    _ = ∫ ω, cavityRootedDepthTestMean n K R L C π a
        (cavityLabeledNoiseDisorderMap n ω) ∂cavityLabeledDisorderLaw n b S₀ S := by
      apply integral_congr_ae
      filter_upwards [hi, cavity_labeled_disorder_good n b S₀ S hb,
        cavity_labeled_disorder_injective n b S₀ S hAtom] with ω hω hg hgi
      exact prior_cavity_labeled_model_depth_mean n K R L C π a ω hgi hg.1 hg.2 hω
    _ = _ := (cavity_labeled_noise_disorder_law n b S₀ S).hasLaw.integral_comp
      (measurable_cavityRootedDepthTestMean n K R L C π a).aestronglyMeasurable

end InvariantIsing

end

end OAI
