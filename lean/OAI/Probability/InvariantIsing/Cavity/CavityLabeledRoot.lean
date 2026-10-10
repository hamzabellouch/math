import OAI.Probability.InvariantIsing.Cavity.CavityLabeledSpin
import OAI.Probability.InvariantIsing.Cavity.CavityRootedSpinTransport

namespace OAI

/-! Labeled coordinates for the actual rooted full Gibbs kernel. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal

namespace InvariantIsing

lemma cavity_labeled_spin_prior_law {d k : ℕ} (n : ℕ)
    (T : LabeledTree n) (g : ForestVertex n → EuclideanSpace ℝ (Fin d))
    (hgood : GoodNoiseTree _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)))
    (ht : 0 < noiseTreeTotal _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)) ∧
      noiseTreeTotal _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)) < ∞)
    (R : Matrix (Fin d) (Fin d) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    MeasurePreserving (cavityLabeledSpinMap n T g)
      (((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod π)
      (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n
        (labeledNoiseJoin _ n (T, markForestOfCoords _ n g))).prod
          (multivariateGaussian 0 R)).prod π) := by
  have hp : MeasurePreserving
      (labeledNoiseLeaf (EuclideanSpace ℝ (Fin d)) n (T, markForestOfCoords _ n g))
      (labeledLeafLaw n T)
      (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n
        (labeledNoiseJoin _ n (T, markForestOfCoords _ n g))) :=
    ⟨measurable_of_countable _, labeledLeafLaw_noiseMap _ n T _ hgood ht⟩
  exact (hp.prod (MeasurePreserving.id (multivariateGaussian 0 R))).prod
    (MeasurePreserving.id π)

lemma cavity_attach_spin_root_prior_law {d k : ℕ} (n : ℕ)
    (R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    MeasurePreserving (cavityAttachSpinRoot n s)
      (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
        (multivariateGaussian 0 R)).prod π)
      ((cavityRootedPriorKernel n R (s, V)).prod π) := by
  refine ⟨measurable_cavityAttachSpinRoot n s, ?_⟩
  rw [cavityRootedPriorKernel, Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply, Measure.dirac_prod]
  change (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
    (multivariateGaussian 0 R)).prod π).map
      (Prod.map (Prod.mk s) (id : Spin k → Spin k)) = _
  simpa only [Measure.map_id, id_eq] using (Measure.map_prod_map
    ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod (multivariateGaussian 0 R)) π
    (measurable_const.prodMk measurable_id) measurable_id).symm

theorem cavity_labeled_rooted_full_spin_law {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (T : LabeledTree n) (g : ForestVertex n → EuclideanSpace ℝ (Fin d))
    (hgood : GoodNoiseTree _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)))
    (ht : 0 < noiseTreeTotal _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)) ∧
      noiseTreeTotal _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)) < ∞)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (hI : Integrable (fun p : (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
      Real.exp (cavityLogFactor K L C
        (cavityLeafSum n s (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) p.1.1) +
          p.1.2 : EuclideanSpace ℝ (Fin d)) p.2))
      (((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod π)) :
    ((((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod π).tilted
      (fun p => cavityLogFactor K L C
        (cavityLeafSum n s (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) p.1.1) +
          p.1.2 : EuclideanSpace ℝ (Fin d)) p.2)).map
            (cavityAttachSpinRoot n s ∘ cavityLabeledSpinMap n T g) =
      cavityRootedFullGibbs n K R L C π
        (s, labeledNoiseJoin _ n (T, markForestOfCoords _ n g)) := by
  let f := cavityAttachSpinRoot (k := k) n s ∘ cavityLabeledSpinMap n T g
  have hp := (cavity_attach_spin_root_prior_law n R s
    (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)) π).comp
      (cavity_labeled_spin_prior_law n T g hgood ht R π)
  let F : CavitySpinState d k n → ℝ :=
    fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2
  have hF : Measurable F := measurable_cavityRootedLogFactor n K L C
  have hi : Integrable (fun z => Real.exp (F z))
      ((cavityRootedPriorKernel n R
        (s, labeledNoiseJoin _ n (T, markForestOfCoords _ n g))).prod π) := by
    rw [← hp.map_eq]
    exact (integrable_map_measure hF.exp.aestronglyMeasurable hp.measurable.aemeasurable).mpr hI
  rw [cavityRootedFullGibbs_eq_tilted n K R L C π _ hi]
  change ((((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod π).tilted
    (F ∘ f)).map f = _
  rw [cavity_tilt_map _ f hp.measurable F hF, hp.map_eq]

end InvariantIsing

end

end OAI
