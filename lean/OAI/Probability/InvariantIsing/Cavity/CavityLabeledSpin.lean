import OAI.Probability.InvariantIsing.Cavity.CavityProjectedSpin

namespace OAI

/-! Labeled representation of the full cavity spin law and its field projection. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal NNReal

namespace InvariantIsing

def cavityLabeledSpinMap {d k : ℕ} (n : ℕ) (T : LabeledTree n)
    (g : ForestVertex n → EuclideanSpace ℝ (Fin d))
    (p : (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k) :
    (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) × Spin k :=
  ((labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) p.1.1, p.1.2), p.2)

lemma measurable_cavityLabeledSpinMap {d k : ℕ} (n : ℕ) (T : LabeledTree n)
    (g : ForestVertex n → EuclideanSpace ℝ (Fin d)) :
    Measurable (cavityLabeledSpinMap (k := k) n T g) := by
  exact (((measurable_of_countable (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g))).comp
    measurable_fst.fst).prodMk measurable_fst.snd).prodMk measurable_snd

lemma measurable_cavityLeafSpinPotential {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (s : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun p : (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d)) × Spin k =>
        cavityLogFactor K L C (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2) := by
  have hp : Measurable (fun p :
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) × Spin k =>
        ((s, p.1), p.2)) := by fun_prop
  have hm := (measurable_cavityRootedLogFactor n K L C).comp hp
  simpa only [Function.comp_def, cavityRootedField] using hm

theorem cavity_labeled_full_spin_law {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (T : LabeledTree n) (g : ForestVertex n → EuclideanSpace ℝ (Fin d))
    (hgood : GoodNoiseTree _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)))
    (ht : 0 < noiseTreeTotal _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)) ∧
      noiseTreeTotal _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)) < ∞)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    ((((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod π).tilted
      (fun p => cavityLogFactor K L C
        (cavityLeafSum n s (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) p.1.1) +
          p.1.2 : EuclideanSpace ℝ (Fin d)) p.2)).map (cavityLabeledSpinMap n T g) =
        cavityResidualSpinFullLaw n K R L C s
          (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)) π := by
  let f := labeledNoiseLeaf (EuclideanSpace ℝ (Fin d)) n (T, markForestOfCoords _ n g)
  have hf : Measurable f := measurable_of_countable _
  have hleaf := labeledLeafLaw_noiseMap _ n T (markForestOfCoords _ n g) hgood ht
  have hbase : (((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod π).map
      (cavityLabeledSpinMap n T g) =
      ((((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n)
        (labeledNoiseJoin _ n (T, markForestOfCoords _ n g))).prod
        (multivariateGaussian 0 R)).prod π) := by
    change (((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod π).map
      (Prod.map (Prod.map f id) id) = _
    rw [← Measure.map_prod_map _ π (hf.prodMap measurable_id) measurable_id,
      ← Measure.map_prod_map _ (multivariateGaussian 0 R) hf measurable_id,
      hleaf, Measure.map_id, Measure.map_id]
  let V : (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) × Spin k → ℝ :=
    fun p => cavityLogFactor K L C (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2
  have hm : Measurable V := by
    exact measurable_cavityLeafSpinPotential n K L C s
  change ((((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod π).tilted
    (V ∘ cavityLabeledSpinMap n T g)).map (cavityLabeledSpinMap n T g) = _
  rw [cavity_tilt_map _ _ (measurable_cavityLabeledSpinMap n T g) V hm, hbase]
  rfl

theorem cavity_labeled_projected_spin_law {d k : ℕ} (n : ℕ)
    (T : LabeledTree n) (g : ForestVertex n → EuclideanSpace ℝ (Fin d))
    (s : EuclideanSpace ℝ (Fin d))
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : L.transpose * R * L = (v : ℝ) • 1)
    (c : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    ((((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod π).tilted
      (fun p => cavityLogFactor 0 L (c • 1)
        (cavityLeafSum n s (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) p.1.1) +
          p.1.2 : EuclideanSpace ℝ (Fin d)) p.2)).map (cavityResidualFieldProjection L) =
      (((labeledLeafLaw n T).prod (vectorGaussianLaw k v)).prod π).tilted
        (fun p => fieldEnergy
          (labeledEnergy n (markForestOfCoords _ n (fun a => cavityProjectField L (g a))) p.1.1
            (cavityProjectField L s) + p.1.2) p.2 + (k : ℝ) * c / 2) := by
  have hy : Measurable (fun α : LabeledLeaf n =>
      cavityLeafSum n s (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) α)) :=
    measurable_of_countable _
  simpa only [cavityProjectField_labeled_sum] using
    cavity_projected_linear_spin_law (labeledLeafLaw n T) R hR L v hcov _ hy c π

end InvariantIsing

end

end OAI
