import OAI.Probability.InvariantIsing.Fields.LabeledAncestrySampling

namespace OAI

/-! Ancestry preservation under any absolutely continuous labeled Gibbs sampling. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma gibbsProbability_absolutelyContinuous {X : Type} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) : gibbsProbability ν H ≪ ν := by
  unfold gibbsProbability
  split_ifs
  · exact Measure.AbsolutelyContinuous.rfl
  · exact tilted_absolutelyContinuous _ _

lemma labeledCascade_total_ae (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    ∀ᵐ ω ∂(labeledCascadeLaw n b : Measure (LabeledTree n)),
      0 < rawTreeTotal n (labeledTreeForget n ω) ∧ rawTreeTotal n (labeledTreeForget n ω) < ⊤ := by
  have h : MeasurePreserving (labeledTreeForget n) (labeledCascadeLaw n b : Measure (LabeledTree n))
      (rawCascadeLaw n b : Measure (RawTree n)) :=
    ⟨measurable_labeledTreeForget n,labeledCascadeLaw_forget n b⟩
  exact h.quasiMeasurePreserving.tendsto_ae.eventually (rawCascade_total_moments n b hb).1

theorem labeled_sampled_ancestry_ae {A S : Type} [MeasurableSpace A] [MeasurableSpace S]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (M : Measure (MarkForest A n)) [IsProbabilityMeasure M]
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcne : ∀ i p, c i p ≠ 0) (s : S)
    (ν : LabeledTree n × MarkForest A n → Measure (LabeledLeaf n))
    (hν : Measurable ν) [∀ p, IsProbabilityMeasure (ν p)]
    (habs : ∀ p, ν p ≪ labeledLeafLaw n p.1) :
    ∀ᵐ q ∂(((labeledCascadeLaw n b : Measure (LabeledTree n)).prod M) ⊗ₘ
        probabilityReplicaKernel ν hν),
      noiseLeafCommonDepth n
        (noiseLeafKeep n c u s (labeledNoiseLeaf A n q.1 (q.2 0)))
        (noiseLeafKeep n c u s (labeledNoiseLeaf A n q.1 (q.2 1))) =
      labeledCommonDepth n (q.2 0) (q.2 1) := by
  have hm : Measurable (fun p : (LabeledTree n × MarkForest A n) × LabeledLeaf n =>
      noiseLeafKeep n c u s (labeledNoiseLeaf A n p.1 p.2)) := by
    apply measurable_from_prod_countable_left
    intro v
    exact (measurable_noiseLeafKeep n hc hu).comp
      (measurable_const.prodMk (measurable_labeledNoiseLeaf A n v))
  have hp (i : ℕ) : Measurable (fun q : (LabeledTree n × MarkForest A n) × (ℕ → LabeledLeaf n) =>
      (q.1,q.2 i)) := measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  have hdepth : Measurable (fun p : LabeledLeaf n × LabeledLeaf n =>
      labeledCommonDepth n p.1 p.2) := measurable_of_countable _
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun ((measurable_noiseLeafCommonDepth n).comp
      ((hm.comp (hp 0)).prodMk (hm.comp (hp 1))))
      (hdepth.comp (((measurable_pi_apply 0).comp measurable_snd).prodMk
        ((measurable_pi_apply 1).comp measurable_snd))))
  have htotal := (measurePreserving_fst (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (ν := M)).quasiMeasurePreserving.tendsto_ae.eventually (labeledCascade_total_ae n b hb)
  filter_upwards [labeled_ancestry_preserved_ae n b M c u hc hu hcne s,htotal] with p hpath htotal
  have hpos := (habs p).ae_le (labeledLeafLaw_positive_weight n p.1 htotal)
  have h0 := (measurePreserving_eval_infinitePi (fun _ : ℕ => ν p) 0).quasiMeasurePreserving.tendsto_ae.eventually hpos
  have h1 := (measurePreserving_eval_infinitePi (fun _ : ℕ => ν p) 1).quasiMeasurePreserving.tendsto_ae.eventually hpos
  filter_upwards [h0,h1] with σ hσ0 hσ1
  exact hpath (σ 0) (σ 1) hσ0 hσ1

end InvariantIsing

end

end OAI
