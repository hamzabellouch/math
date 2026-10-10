import OAI.Analysis.CircleDomains.Topology.PlateauNeighborhoods
import OAI.Analysis.CircleDomains.Sobolev.PositivePartitionSmoothing

namespace OAI

/-! Exact constant values under the constructed positive smoothing. -/

open Set
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem partition_samples_within_plateau
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (center : ι → EuclideanPlane) (A V : Set EuclideanPlane)
    (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (hW : ∀j, W j ⊆ plateauNeighborhood A V (center j)) :
    ∀x ∈ A, ∀j, ρ.weight j x ≠ 0 → W j ⊆ V := by
  intro x hx j hj
  have hxW := hsub j (subset_tsupport (ρ.weight j) hj)
  exact (hW j).trans (plateauNeighborhood_subset_of_meets (hW j hxW) hx)

theorem interval_smoothing_eq_on_plateau
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (f w : EuclideanPlane → ℝ) (A V : Set EuclideanPlane) (c : ℝ)
    (hA : A ⊆ Ω) (hf : ∀x ∈ V, f x = c)
    (hpatch : ∀x ∈ A, ∀j, ρ.weight j x ≠ 0 → W j ⊆ V)
    (hinterval : ∀x ∈ Ω, ∀r s : ℝ,
      (∀j, ρ.weight j x ≠ 0 → ∀y ∈ W j, f y ∈ Icc r s) → w x ∈ Icc r s) :
    ∀x ∈ A, w x = c := by
  intro x hx
  have hh := hinterval x (hA hx) c c (by
    intro j hj y hy
    rw [hf y (hpatch x hx j hj hy)]
    exact ⟨le_rfl, le_rfl⟩)
  exact le_antisymm hh.2 hh.1

end CircleDomainRigidity

end

end OAI
