import OAI.Probability.InvariantIsing.Cavity.CavityBaseCutoffFactor
import OAI.Probability.InvariantIsing.Cavity.CavityCutoffMap
import OAI.Probability.InvariantIsing.Cavity.CavitySpinSplit

namespace OAI

/-! The restricted base/cavity test in the exact product coordinates:
the shared cascade leaf stays with the base Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

def cavityPairLeafSwap {N n depth : ℕ}
    (x : (Spin N × Spin n) × LabeledLeaf depth) :
    (Spin N × LabeledLeaf depth) × Spin n := ((x.1.1,x.2),x.1.2)

def cavityPairLeafUnswap {N n depth : ℕ}
    (x : (Spin N × LabeledLeaf depth) × Spin n) :
    (Spin N × Spin n) × LabeledLeaf depth := ((x.1.1,x.2),x.1.2)

lemma cavity_pair_leaf_swap_preserving (N n depth : ℕ) (T : LabeledTree depth) :
    MeasurePreserving (cavityPairLeafSwap (N := N) (n := n) (depth := depth))
      (((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
        (labeledLeafLaw depth T))
      ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n)) := by
  have h₁ := measurePreserving_prodAssoc (uniformSpinPrior N : Measure (Spin N))
    (uniformSpinPrior n : Measure (Spin n)) (labeledLeafLaw depth T)
  have h₂ := (MeasurePreserving.id (uniformSpinPrior N : Measure (Spin N))).prod
    (Measure.measurePreserving_swap (μ := (uniformSpinPrior n : Measure (Spin n)))
      (ν := labeledLeafLaw depth T))
  have h₃ := (measurePreserving_prodAssoc (uniformSpinPrior N : Measure (Spin N))
    (labeledLeafLaw depth T) (uniformSpinPrior n : Measure (Spin n))).symm MeasurableEquiv.prodAssoc
  exact h₃.comp (h₂.comp h₁)

theorem cavity_base_restricted_product {N n depth : ℕ} (T : LabeledTree depth)
    (J : Spin N × LabeledLeaf depth → ℝ)
    (W : (Spin N × Spin n) × LabeledLeaf depth → ℝ)
    (hj : Integrable (fun x => Real.exp (J x))
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T))
    (hfull : Integrable (fun x => Real.exp (J (x.1.1,x.2) + W x))
      (((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
        (labeledLeafLaw depth T)))
    (s : Set ((Spin N × Spin n) × LabeledLeaf depth))
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ) :
    cavityCutoffReplicaMean
      (((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
        (labeledLeafLaw depth T)) (fun x => J (x.1.1,x.2) + W x) s F =
    cavityWeightedReplicaMean
      (((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted J).prod
        (uniformSpinPrior n))
      ((cavityPairLeafUnswap ⁻¹' s).indicator (fun x => Real.exp (W (cavityPairLeafUnswap x))))
      (fun σ => F (fun i => cavityPairLeafUnswap (σ i))) := by
  let μ := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let π := (uniformSpinPrior n : Measure (Spin n))
  let ν := ((uniformSpinPrior N : Measure (Spin N)).prod π).prod (labeledLeafLaw depth T)
  let V := W ∘ cavityPairLeafUnswap
  have hp := cavity_pair_leaf_swap_preserving N n depth T
  have he : Integrable (fun x => Real.exp (J x.1 + V x)) (μ.prod π) :=
    (hp.integrable_comp (measurable_of_countable _).aestronglyMeasurable).mp hfull
  have hc := cavity_cutoff_replica_map ν (μ.prod π) cavityPairLeafSwap hp
    (fun x => J x.1 + V x) (cavityPairLeafUnswap ⁻¹' s)
    (fun σ => F (fun i => cavityPairLeafUnswap (σ i)))
  exact hc.trans (cavity_base_cutoff_indicator μ π J V hj he
    (cavityPairLeafUnswap ⁻¹' s) (fun σ => F (fun i => cavityPairLeafUnswap (σ i))))

end InvariantIsing

end

end OAI
