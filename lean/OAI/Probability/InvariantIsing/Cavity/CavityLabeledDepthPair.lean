import OAI.Probability.InvariantIsing.Cavity.CavityLabeledRootPair
import OAI.Probability.InvariantIsing.Cavity.CavityRootedDepthTransport

namespace OAI

/-! Labeled common depths in the actual rooted full Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal

namespace InvariantIsing

theorem cavity_labeled_rooted_depth_pair {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (T : LabeledTree n) (g : ForestVertex n → EuclideanSpace ℝ (Fin d))
    (hg : Function.Injective g)
    (hgood : GoodNoiseTree _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)))
    (ht : 0 < noiseTreeTotal _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)) ∧
      noiseTreeTotal _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)) < ∞)
    (hI : Integrable (fun p : (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
      Real.exp (cavityLogFactor K L C
        (cavityLeafSum n s (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) p.1.1) +
          p.1.2 : EuclideanSpace ℝ (Fin d)) p.2))
      (((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod (uniformSpinPrior k)))
    (a : ℕ → ℝ) :
    (∫ σ, cavityRootedDepthTest a σ
      ∂Measure.infinitePi (fun _ : ℕ => cavityRootedFullGibbs n K R L C
        (uniformSpinPrior k) (s, labeledNoiseJoin _ n (T, markForestOfCoords _ n g)))) =
    referenceReplicaMean
      (((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod (uniformSpinPrior k))
      (fun p => cavityLogFactor K L C
        (cavityLeafSum n s (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) p.1.1) +
          p.1.2 : EuclideanSpace ℝ (Fin d)) p.2)
      (fun σ : Fin 2 → (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
        a (labeledCommonDepth n (σ 0).1.1 (σ 1).1.1)) := by
  let ν := cavityRootedFullGibbs n K R L C (uniformSpinPrior k)
    (s, labeledNoiseJoin _ n (T, markForestOfCoords _ n g))
  let μ := (((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod
    (uniformSpinPrior k)).tilted (fun p => cavityLogFactor K L C
      (cavityLeafSum n s (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) p.1.1) +
        p.1.2 : EuclideanSpace ℝ (Fin d)) p.2)
  let f := cavityAttachSpinRoot (k := k) n s ∘ cavityLabeledSpinMap n T g
  have hf : Measurable f := (measurable_cavityAttachSpinRoot n s).comp
    (measurable_cavityLabeledSpinMap n T g)
  have hmap : μ.map f = ν :=
    cavity_labeled_rooted_full_spin_law n K R L C s T g hgood ht (uniformSpinPrior k) hI
  let F : (Fin 2 → CavitySpinState d k n) → ℝ := fun σ =>
    a (cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1)
  have hF : Measurable F := by
    have hc : Measurable (fun σ : Fin 2 → CavitySpinState d k n =>
        cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1) :=
      (cavityCommonMarkDepth_measurable n).comp
        (show Measurable (fun σ : Fin 2 → CavitySpinState d k n =>
          ((σ 0).1.2.1, (σ 1).1.2.1)) from by fun_prop)
    exact (measurable_of_countable a).comp hc
  have hprefix : MeasurePreserving (fun σ : ℕ → CavitySpinState d k n =>
      fun i : Fin 2 => σ i) (Measure.infinitePi (fun _ : ℕ => ν))
      (Measure.pi (fun _ : Fin 2 => ν)) :=
    ⟨Measurable.of_eval (fun i => measurable_pi_apply (i : ℕ)), replica_prefix_map ν 2⟩
  have hpi : MeasurePreserving
      (fun σ : Fin 2 → (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
        fun i => f (σ i))
      (Measure.pi (fun _ : Fin 2 => μ)) (Measure.pi (fun _ : Fin 2 => ν)) := by
    refine ⟨Measurable.of_eval (fun i => hf.comp (measurable_pi_apply i)), ?_⟩
    simpa only [hmap] using Measure.pi_map_pi
      (μ := fun _ : Fin 2 => μ) (f := fun _ : Fin 2 => f) (fun _ => hf.aemeasurable)
  rw [cavity_reference_pair_eq_tilted _ _ hI]
  calc
    _ = ∫ σ, F σ ∂Measure.pi (fun _ : Fin 2 => ν) := by
      simpa only [Function.comp_def, F, cavityRootedDepthTest, Fin.val_zero, Fin.val_one, ν] using
        hprefix.hasLaw.integral_comp hF.aestronglyMeasurable
    _ = _ := by
      have hi := (hpi.hasLaw.integral_comp hF.aestronglyMeasurable).symm
      simpa only [Function.comp_def, F, f, cavityAttachSpinRoot, cavityLabeledSpinMap,
        cavityCommonMarkDepth_labeled n T g hg] using hi

end InvariantIsing

end

end OAI
