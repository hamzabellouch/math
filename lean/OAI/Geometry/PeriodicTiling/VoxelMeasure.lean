import OAI.Geometry.PeriodicTiling.VoxelCubeMeasure
import Mathlib.Topology.MetricSpace.Bounded

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set MeasureTheory
open scoped ENNReal

theorem Thickening_eq_iUnion {d : ℕ} (F : Finset (Lattice d)) :
    Thickening F = ⋃ z ∈ F, unitVoxel (castLattice z) := by
  ext x
  simp only [mem_Thickening, Set.mem_iUnion, mem_unitVoxel, exists_prop]

theorem thickening_isCompact {d : ℕ} (F : Finset (Lattice d)) :
    IsCompact (Thickening F) := by
  rw [Thickening_eq_iUnion]
  exact F.isCompact_biUnion (fun z _ => unitVoxel_isCompact (castLattice z))

theorem thickening_isClosed {d : ℕ} (F : Finset (Lattice d)) :
    IsClosed (Thickening F) := (thickening_isCompact F).isClosed

theorem thickening_measurableSet {d : ℕ} (F : Finset (Lattice d)) :
    MeasurableSet (Thickening F) := (thickening_isClosed F).measurableSet

theorem thickening_isBounded {d : ℕ} (F : Finset (Lattice d)) :
    Bornology.IsBounded (Thickening F) := (thickening_isCompact F).isBounded

theorem thickening_volume {d : ℕ} (F : Finset (Lattice d)) :
    volume (Thickening F) = (F.card : ℝ≥0∞) := by
  classical
  rw [Thickening_eq_iUnion]
  rw [measure_biUnion_finset₀
    (fun z _ z' _ hne => unitVoxel_aedisjoint_int hne)
    (fun z _ => (unitVoxel_measurableSet (castLattice z)).nullMeasurableSet)]
  simp [unitVoxel_volume]

theorem thickening_aedisjoint_of_disjoint {d : ℕ}
    {S T : Finset (Lattice d)} (h : Disjoint S T) :
    AEDisjoint volume (Thickening S) (Thickening T) := by
  classical
  simp only [Thickening_eq_iUnion, AEDisjoint.iUnion_left_iff,
    AEDisjoint.iUnion_right_iff]
  intro z hz z' hz'
  apply unitVoxel_aedisjoint_int
  intro heq
  subst z'
  exact Finset.disjoint_left.mp h hz' hz

theorem thickening_inter_measure_zero_of_disjoint {d : ℕ}
    {S T : Finset (Lattice d)} (h : Disjoint S T) :
    volume (Thickening S ∩ Thickening T) = 0 :=
  (thickening_aedisjoint_of_disjoint h).eq

end PeriodicTilingThree

end

end OAI
