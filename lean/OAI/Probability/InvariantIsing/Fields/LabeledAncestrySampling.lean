import OAI.Probability.InvariantIsing.Fields.LabeledScaledAncestry

namespace OAI

/-! Almost-sure ancestry preservation on the labeled sampling space. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal
namespace InvariantIsing
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S]

lemma labeled_ancestry_preserved_ae (n : ℕ) (b : ℕ → ℝ)
    (ν : Measure (MarkForest A n)) [IsProbabilityMeasure ν]
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcne : ∀ i p, c i p ≠ 0) (s : S) :
    ∀ᵐ p ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod ν,
      ∀ v w : LabeledLeaf n, labeledLeafWeight n p.1 v ≠ 0 → labeledLeafWeight n p.1 w ≠ 0 →
        noiseLeafCommonDepth n
          (noiseLeafKeep n c u s (labeledNoiseLeaf A n p v))
          (noiseLeafKeep n c u s (labeledNoiseLeaf A n p w)) = labeledCommonDepth n v w := by
  rw [ae_all_iff]
  intro v
  rw [ae_all_iff]
  intro w
  have hm (a : LabeledLeaf n) : Measurable (fun p : LabeledTree n × MarkForest A n =>
      noiseLeafKeep n c u s (labeledNoiseLeaf A n p a)) :=
    (measurable_noiseLeafKeep n hc hu).comp
      (measurable_const.prodMk (measurable_labeledNoiseLeaf A n a))
  have he : MeasurableSet {p : LabeledTree n × MarkForest A n |
      noiseLeafCommonDepth n (noiseLeafKeep n c u s (labeledNoiseLeaf A n p v))
        (noiseLeafKeep n c u s (labeledNoiseLeaf A n p w)) = labeledCommonDepth n v w} :=
    measurableSet_eq_fun ((measurable_noiseLeafCommonDepth n).comp ((hm v).prodMk (hm w))) measurable_const
  have hs : MeasurableSet {p : LabeledTree n × MarkForest A n |
      labeledLeafWeight n p.1 v ≠ 0 → labeledLeafWeight n p.1 w ≠ 0 →
        noiseLeafCommonDepth n (noiseLeafKeep n c u s (labeledNoiseLeaf A n p v))
          (noiseLeafKeep n c u s (labeledNoiseLeaf A n p w)) = labeledCommonDepth n v w} :=
    (measurableSet_eq_fun ((measurable_labeledLeafWeight n v).comp measurable_fst) measurable_const).compl.imp
      ((measurableSet_eq_fun ((measurable_labeledLeafWeight n w).comp measurable_fst) measurable_const).compl.imp he)
  apply (Measure.ae_prod_iff_ae_ae hs).mpr
  apply (Measure.ae_ae_comm hs).mpr
  exact ae_of_all _ fun z => (labeledCascade_scaled_simple_ae n b c u hcne s z).mono
    (fun ω hω hv hw => noiseLeafCommonDepth_keep_labeled n c u s ω z hω v w hv hw)

lemma labeledLeafLaw_positive_weight (n : ℕ) (ω : LabeledTree n)
    (hω : 0 < rawTreeTotal n (labeledTreeForget n ω) ∧ rawTreeTotal n (labeledTreeForget n ω) < ∞) :
    ∀ᵐ v ∂labeledLeafLaw n ω, labeledLeafWeight n ω v ≠ 0 := by
  rw [labeledLeafLaw, normalizeMass, ite_eq_left (by simpa only [labeledLeafMass_univ] using hω)]
  apply Measure.ae_smul_measure
  rw [ae_iff]
  have hz : {v : LabeledLeaf n | ¬labeledLeafWeight n ω v ≠ 0} =
      {v : LabeledLeaf n | labeledLeafWeight n ω v = 0} := by ext v; simp
  rw [hz,labeledLeafMass,withDensity_apply _ (Set.to_countable _).measurableSet]
  apply setLIntegral_eq_zero (Set.to_countable _).measurableSet
  intro v hv
  exact hv

end InvariantIsing

end

end OAI
