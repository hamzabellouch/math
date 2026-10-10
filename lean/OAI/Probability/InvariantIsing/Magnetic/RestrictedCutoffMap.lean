import OAI.Probability.InvariantIsing.Cavity.CavityCutoffMap
import OAI.Probability.InvariantIsing.Magnetic.RestrictedProductPrior

namespace OAI

/-! Cutoffs commute with the constrained spin product decomposition. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

theorem restricted_spin_cutoff_split {N n depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (T : LabeledTree depth) (H : (Spin N × Spin n) × LabeledLeaf depth → ℝ)
    (s : Set ((Spin N × Spin n) × LabeledLeaf depth))
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ) :
    cavityCutoffReplicaMean
      (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S C)
        (cavityProductSlice_nonempty S hS C hC) : Measure (Spin (N+n))) T)
      (fun x => H (cavitySpinSplit N n x.1,x.2))
      {x | (cavitySpinSplit N n x.1,x.2) ∈ s}
      (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) =
    cavityCutoffReplicaMean
      (((restrictedSpinPrior S hS : Measure (Spin N)).prod (restrictedSpinPrior C hC)).prod
        (labeledLeafLaw depth T)) H s F :=
  cavity_cutoff_replica_map _ _ _ ((restricted_cavity_spin_split_prior S hS C hC).prod
    (MeasurePreserving.id (labeledLeafLaw depth T))) H s F

end InvariantIsing

end

end OAI
