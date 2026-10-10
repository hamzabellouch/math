import OAI.Probability.InvariantIsing.Cavity.CavityCutoffSubtype
import OAI.Probability.InvariantIsing.Cavity.CavitySpinSplit

namespace OAI

/-! Cutoff replica tests commute with the exact split of the uniform
spin law into its base and cavity coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

lemma cavity_cutoff_replica_map {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable X] [Countable Y] [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → Y) (hf : MeasurePreserving f μ ν)
    (H : Y → ℝ) (s : Set Y) (F : (Fin 2 → Y) → ℝ) :
    cavityCutoffReplicaMean μ (H ∘ f) (f ⁻¹' s) (fun σ => F (f ∘ σ)) =
      cavityCutoffReplicaMean ν H s F := by
  have hn := referenceReplicaMean_map hf (measurable_of_countable H)
    (measurable_of_countable (fun σ : Fin 2 → Y => if ∀ i, σ i ∈ s then F σ else 0))
  have hd := referenceReplicaMean_map hf (measurable_of_countable H)
    (measurable_of_countable (fun σ : Fin 2 → Y => if ∀ i, σ i ∈ s then (1 : ℝ) else 0))
  exact congrArg₂ (fun a b : ℝ => a / b) hn hd

lemma cavity_spin_pair_leaf_prior (N n depth : ℕ) (T : LabeledTree depth) :
    MeasurePreserving (fun x : Spin (N+n) × LabeledLeaf depth =>
      (cavitySpinSplit N n x.1,x.2))
      (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
      (((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
        (labeledLeafLaw depth T)) :=
  (cavity_spin_split_prior N n).prod (MeasurePreserving.id (labeledLeafLaw depth T))

theorem cavity_spin_cutoff_split {N n depth : ℕ} (T : LabeledTree depth)
    (H : (Spin N × Spin n) × LabeledLeaf depth → ℝ)
    (s : Set ((Spin N × Spin n) × LabeledLeaf depth))
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ) :
    cavityCutoffReplicaMean
      (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
      (fun x => H (cavitySpinSplit N n x.1,x.2))
      {x | (cavitySpinSplit N n x.1,x.2) ∈ s}
      (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) =
    cavityCutoffReplicaMean
      (((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
        (labeledLeafLaw depth T)) H s F :=
  cavity_cutoff_replica_map _ _ _ (cavity_spin_pair_leaf_prior N n depth T) H s F

end InvariantIsing

end

end OAI
