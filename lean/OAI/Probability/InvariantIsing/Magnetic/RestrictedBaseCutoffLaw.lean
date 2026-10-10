import OAI.Probability.InvariantIsing.Cavity.CavityBaseRestrictedLaw
import OAI.Probability.InvariantIsing.Magnetic.RestrictedLogMap
import OAI.Probability.InvariantIsing.Cavity.CavityCutoffMap
import OAI.Probability.InvariantIsing.Cavity.CavitySpinSplit

namespace OAI

/-! The restricted base/cavity test in the exact product coordinates:
the shared cascade leaf stays with the base Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

theorem restricted_base_cutoff_product_law {N n depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (T : LabeledTree depth)
    (J : Spin N × LabeledLeaf depth → ℝ)
    (W : (Spin N × Spin n) × LabeledLeaf depth → ℝ)
    (hj : Integrable (fun x => Real.exp (J x))
      (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T))
    (hfull : Integrable (fun x => Real.exp (J (x.1.1,x.2) + W x))
      (((restrictedSpinPrior S hS : Measure (Spin N)).prod (restrictedSpinPrior Cset hCset)).prod
        (labeledLeafLaw depth T)))
    (s : Set ((Spin N × Spin n) × LabeledLeaf depth))
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ) :
    cavityCutoffReplicaMean
      (((restrictedSpinPrior S hS : Measure (Spin N)).prod (restrictedSpinPrior Cset hCset)).prod
        (labeledLeafLaw depth T)) (fun x => J (x.1.1,x.2) + W x) s F =
    cavityWeightedReplicaMean
      (((labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).tilted J).prod
        (restrictedSpinPrior Cset hCset))
      ((cavityPairLeafUnswap ⁻¹' s).indicator (fun x => Real.exp (W (cavityPairLeafUnswap x))))
      (fun σ => F (fun i => cavityPairLeafUnswap (σ i))) := by
  let μ := labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T
  let π := (restrictedSpinPrior Cset hCset : Measure (Spin n))
  let ν := ((restrictedSpinPrior S hS : Measure (Spin N)).prod π).prod (labeledLeafLaw depth T)
  let V := W ∘ cavityPairLeafUnswap
  have hp := restricted_pair_leaf_swap_preserving S hS Cset hCset T
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
