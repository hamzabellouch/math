import OAI.Probability.InvariantIsing.Fields.LabeledReplicaAncestry

namespace OAI

/-! Sampled ancestry with the forest represented by its independent coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

theorem coordinate_sampled_ancestry_ae {A S : Type} [MeasurableSpace A] [MeasurableSpace S]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure A)
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcne : ∀ i p, c i p ≠ 0) (s : S)
    (ν : LabeledTree n × (ForestVertex n → A) → Measure (LabeledLeaf n))
    (hν : Measurable ν) [∀ p, IsProbabilityMeasure (ν p)]
    (habs : ∀ p, ν p ≪ labeledLeafLaw n p.1) :
    let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi fun a : ForestVertex n => (μ (forestVertexDepth n a) : Measure A))
    ∀ᵐ q ∂P ⊗ₘ probabilityReplicaKernel ν hν,
      noiseLeafCommonDepth n
        (noiseLeafKeep n c u s (labeledNoiseLeaf A n
          (q.1.1,markForestOfCoords A n q.1.2) (q.2 0)))
        (noiseLeafKeep n c u s (labeledNoiseLeaf A n
          (q.1.1,markForestOfCoords A n q.1.2) (q.2 1))) =
      labeledCommonDepth n (q.2 0) (q.2 1) := by
  intro P
  have hcoord : MeasurePreserving (fun p : LabeledTree n × (ForestVertex n → A) =>
      (p.1,markForestOfCoords A n p.2)) P
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
        (markForestLaw A n μ : Measure (MarkForest A n))) :=
    (MeasurePreserving.id _).prod
      ⟨measurable_markForestOfCoords A n,markForestOfCoords_law A n μ⟩
  have hroot := hcoord.quasiMeasurePreserving.tendsto_ae.eventually
    (labeled_ancestry_preserved_ae n b (markForestLaw A n μ : Measure (MarkForest A n)) c u hc hu hcne s)
  have hm : Measurable (fun p : (LabeledTree n × (ForestVertex n → A)) × LabeledLeaf n =>
      noiseLeafKeep n c u s (labeledNoiseLeaf A n
        (p.1.1,markForestOfCoords A n p.1.2) p.2)) := by
    apply measurable_from_prod_countable_left
    intro α
    exact (measurable_noiseLeafKeep n hc hu).comp
      (measurable_const.prodMk ((measurable_labeledNoiseLeaf A n α).comp hcoord.measurable))
  have hp (i : ℕ) : Measurable (fun q : (LabeledTree n × (ForestVertex n → A)) ×
      (ℕ → LabeledLeaf n) => (q.1,q.2 i)) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun ((measurable_noiseLeafCommonDepth n).comp
      ((hm.comp (hp 0)).prodMk (hm.comp (hp 1))))
      ((measurable_of_countable (fun p : LabeledLeaf n × LabeledLeaf n =>
        labeledCommonDepth n p.1 p.2)).comp
        (((measurable_pi_apply 0).comp measurable_snd).prodMk
          ((measurable_pi_apply 1).comp measurable_snd))))
  have ht := (measurePreserving_fst (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (ν := Measure.infinitePi fun a : ForestVertex n =>
      (μ (forestVertexDepth n a) : Measure A))).quasiMeasurePreserving.tendsto_ae.eventually
        (labeledCascade_total_ae n b hb)
  filter_upwards [hroot,ht] with p hpath htotal
  have hpos := (habs p).ae_le (labeledLeafLaw_positive_weight n p.1 htotal)
  have h0 := (measurePreserving_eval_infinitePi (fun _ : ℕ => ν p) 0).quasiMeasurePreserving.tendsto_ae.eventually hpos
  have h1 := (measurePreserving_eval_infinitePi (fun _ : ℕ => ν p) 1).quasiMeasurePreserving.tendsto_ae.eventually hpos
  filter_upwards [h0,h1] with σ hσ0 hσ1
  exact hpath (σ 0) (σ 1) hσ0 hσ1

end InvariantIsing

end

end OAI
