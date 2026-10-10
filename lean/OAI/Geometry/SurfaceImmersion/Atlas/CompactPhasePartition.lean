import OAI.Geometry.Immersion.ClosedSurface.OscillatoryModel
import Mathlib.Geometry.Manifold.PartitionOfUnity

namespace OAI

/-!
Finite smooth partitions on the compact set on which a phase correction is
required.  The coefficients have compact support inside the supplied open
phase domains.  These are ordinary partition coefficients, so splitting a
tensor target does not require taking square roots.
-/

noncomputable section

open Set Manifold TopologicalSpace
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.PhasePartitions

open SmallModes (Base)

/-- A finite smooth partition on a compact target set, with compact supports
subordinate to the prescribed phase domains. -/
structure CompactPhasePartition (ι : Type*) [Fintype ι]
    (K : Set Base) (U : ι → Set Base) where
  weight : ι → Base → ℝ
  smooth : ∀ i, ContDiff ℝ ∞ (weight i)
  nonneg : ∀ i x, 0 ≤ weight i x
  le_one : ∀ i x, weight i x ≤ 1
  compact_support : ∀ i, HasCompactSupport (weight i)
  subordinate : ∀ i, tsupport (weight i) ⊆ U i
  sum_eq_one : ∀ x ∈ K, ∑ i, weight i x = 1

namespace CompactPhasePartition

variable {ι : Type*} [Fintype ι] {K : Set Base} {U : ι → Set Base}

/-- The actual compact topological support of one partition coefficient. -/
def supportCompact (P : CompactPhasePartition ι K U) (i : ι) : Compacts Base :=
  ⟨tsupport (P.weight i), P.compact_support i⟩

@[simp] theorem coe_supportCompact (P : CompactPhasePartition ι K U) (i : ι) :
    (P.supportCompact i : Set Base) = tsupport (P.weight i) := rfl

theorem supportCompact_subset (P : CompactPhasePartition ι K U) (i : ι) :
    (P.supportCompact i : Set Base) ⊆ U i := P.subordinate i

end CompactPhasePartition

/-- A finite open cover of a compact subset of the phase plane admits compactly
supported smooth partition coefficients indexed by that same cover. -/
theorem exists_compact_phase_partition {ι : Type*} [Fintype ι]
    {K : Set Base} (hK : IsCompact K) (U : ι → Set Base)
    (hU : ∀ i, IsOpen (U i)) (hcover : K ⊆ ⋃ i, U i) :
    Nonempty (CompactPhasePartition ι K U) := by
  classical
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Base)
  let V : ι → Set Base := fun i => U i ∩ Metric.ball 0 r
  have hV : ∀ i, IsOpen (V i) := fun i => (hU i).inter Metric.isOpen_ball
  have hcoverV : K ⊆ ⋃ i, V i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨i, hi, hr hx⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, Base))
    hK.isClosed V hV hcoverV
  refine ⟨{
    weight := fun i => ρ i
    smooth := fun i => (ρ i).contMDiff.contDiff
    nonneg := ρ.nonneg
    le_one := ρ.le_one
    compact_support := ?_
    subordinate := fun i x hx => (hρ i hx).1
    sum_eq_one := ?_ }⟩
  · intro i
    apply (isCompact_closedBall (0 : Base) r).of_isClosed_subset (isClosed_tsupport _)
    intro x hx
    exact Metric.ball_subset_closedBall ((hρ i hx).2)
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx

/-- For a family of local phase domains, compactness first selects finitely
many domains and then constructs the supported partition on those domains. -/
theorem exists_finite_compact_phase_partition {ι : Type*}
    {K : Set Base} (hK : IsCompact K) (U : ι → Set Base)
    (hU : ∀ i, IsOpen (U i)) (hcover : K ⊆ ⋃ i, U i) :
    ∃ s : Finset ι, Nonempty (CompactPhasePartition s K (fun i => U i)) := by
  classical
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU hcover
  refine ⟨s, exists_compact_phase_partition hK (fun i : s => U i)
    (fun i => hU i) ?_⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
  exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩

end ClosedSurfaceR4.PhasePartitions

end

end OAI
