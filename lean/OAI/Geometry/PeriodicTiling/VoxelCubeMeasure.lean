import OAI.Geometry.PeriodicTiling.VoxelGeometry
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.AEDisjoint

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set MeasureTheory Filter
open scoped ENNReal

theorem unitVoxel_volume {d : ℕ} (c : Space d) :
    volume (unitVoxel c) = 1 := by
  rw [unitVoxel_eq_Icc, Real.volume_Icc_pi]
  simp

theorem unitCube_volume (d : ℕ) : volume (unitCube d) = 1 := by
  simpa only [unitVoxel, sub_zero, Set.ofPred_mem_eq] using
    unitVoxel_volume (0 : Space d)

theorem openUnitVoxel_volume {d : ℕ} (c : Space d) :
    volume (openUnitVoxel c) = 1 := by
  rw [openUnitVoxel, Real.volume_pi_Ioo]
  simp

theorem openUnitVoxel_ae_eq_unitVoxel {d : ℕ} (c : Space d) :
    openUnitVoxel c =ᵐ[volume] unitVoxel c := by
  rw [unitVoxel_eq_Icc]
  exact Measure.univ_pi_Ioo_ae_eq_Icc

theorem unitVoxel_frontier_volume_zero {d : ℕ} (c : Space d) :
    volume (frontier (unitVoxel c)) = 0 := by
  have hnull : volume (unitVoxel c \ openUnitVoxel c) = 0 :=
    ae_le_set.mp (openUnitVoxel_ae_eq_unitVoxel c).symm.le
  apply measure_mono_null _ hnull
  intro x hx
  refine ⟨(unitVoxel_isClosed c).frontier_subset hx, ?_⟩
  intro ho
  exact hx.2 (interior_maximal (openUnitVoxel_subset c)
    (isOpen_openUnitVoxel c) ho)

theorem unitVoxel_inter_volume_pos {d : ℕ} (a b : Space d)
    (h : ∀ i, |b i - a i| < 1) :
    0 < volume (unitVoxel a ∩ unitVoxel b) := by
  rw [unitVoxel_inter_eq_Icc, Real.volume_Icc_pi]
  apply bot_lt_iff_ne_bot.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  apply sub_pos.mpr
  apply max_lt
  · apply lt_min
    · linarith
    · have hi := (abs_lt.mp (h i)).1
      linarith
  · apply lt_min
    · have hi := (abs_lt.mp (h i)).2
      linarith
    · linarith

theorem closedBall_volume {d : ℕ} (c : Space d) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall c r) = ENNReal.ofReal ((2 * r) ^ d) := by
  simpa using Real.volume_pi_closedBall c hr

theorem closedBall_ae_eq_ball {d : ℕ} (c : Space d) {r : ℝ} (hr : 0 < r) :
    Metric.closedBall c r =ᵐ[volume] Metric.ball c r := by
  rw [closedBall_pi c hr.le, ball_pi c hr]
  simp only [Real.closedBall_eq_Icc, Real.ball_eq_Ioo]
  exact Measure.pi_Ioo_ae_eq_pi_Icc.symm

theorem closedBall_frontier_volume_zero {d : ℕ} (c : Space d)
    {r : ℝ} (hr : 0 < r) :
    volume (frontier (Metric.closedBall c r)) = 0 := by
  have hnull : volume (Metric.closedBall c r \ Metric.ball c r) = 0 :=
    ae_le_set.mp (closedBall_ae_eq_ball c hr).le
  apply measure_mono_null _ hnull
  intro x hx
  refine ⟨Metric.isClosed_closedBall.frontier_subset hx, ?_⟩
  intro hb
  exact hx.2 (Metric.ball_subset_interior_closedBall hb)

theorem unitVoxel_aedisjoint_int {d : ℕ} {z z' : Lattice d} (hne : z ≠ z') :
    AEDisjoint volume (unitVoxel (castLattice z)) (unitVoxel (castLattice z')) := by
  exact (openUnitVoxel_disjoint_unitVoxel_int hne).aedisjoint.congr
    (openUnitVoxel_ae_eq_unitVoxel _).symm EventuallyEq.rfl

end PeriodicTilingThree

end

end OAI
