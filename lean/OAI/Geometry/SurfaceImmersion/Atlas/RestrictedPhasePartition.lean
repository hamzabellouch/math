import OAI.Geometry.SurfaceImmersion.Geometry.SplitSupportedBounds

namespace OAI

/-! Restrict a fixed partition to any smaller target support, preserving
its numerical derivative constants exactly. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.PhasePartitions.CompactPhasePartition
open SmallModes
variable {ι : Type*} [Fintype ι] {K : Compacts Base} {U : ι → Set Base}

def restrictTarget (P : CompactPhasePartition ι (K : Set Base) U)
    (L : Compacts Base) (hL : (L : Set Base) ⊆ K) :
    CompactPhasePartition ι (L : Set Base) U where
  weight := P.weight
  smooth := P.smooth
  nonneg := P.nonneg
  le_one := P.le_one
  compact_support := P.compact_support
  subordinate := P.subordinate
  sum_eq_one := fun x hx => P.sum_eq_one x (hL hx)

lemma restrictTarget_splitConstant (P : CompactPhasePartition ι (K : Set Base) U)
    (L : Compacts Base) (hL : (L : Set Base) ⊆ K) (m : ℕ) :
    (P.restrictTarget L hL).splitConstant m = P.splitConstant m := rfl

end ClosedSurfaceR4.PhasePartitions.CompactPhasePartition

end

end OAI
