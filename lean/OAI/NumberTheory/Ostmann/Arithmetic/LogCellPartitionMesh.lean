import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionBoxes
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellMeshCounts

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open PrimeCellMeshBudget
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem boxLower_le_boxUpper {lo hi η : ι → ℝ} (h : ∀ i, lo i ≤ hi i)
    (j : GridBoxIndex lo hi η) (i : ι) : boxLower lo hi η j i ≤ boxUpper lo hi η j i :=
  gridPoint_mono (h i) (Nat.le_succ _)

omit [Fintype ι] [DecidableEq ι] in
theorem boxLower_mem_interval {lo hi η : ι → ℝ} (h : ∀ i, lo i ≤ hi i)
    (j : GridBoxIndex lo hi η) (i : ι) : boxLower lo hi η j i ∈ Set.Icc (lo i) (hi i) :=
  gridPoint_mem (h i) (j i).isLt.le

omit [Fintype ι] [DecidableEq ι] in
theorem boxUpper_mem_interval {lo hi η : ι → ℝ} (h : ∀ i, lo i ≤ hi i)
    (j : GridBoxIndex lo hi η) (i : ι) : boxUpper lo hi η j i ∈ Set.Icc (lo i) (hi i) :=
  gridPoint_mem (h i) (show (j i).val+1 ≤ gridCount (lo i) (hi i) (η i) by omega)

omit [Fintype ι] [DecidableEq ι] in
theorem box_width_le {lo hi η : ι → ℝ} (h : ∀ i, lo i ≤ hi i) (hη : ∀ i, 0 < η i)
    (j : GridBoxIndex lo hi η) (i : ι) : boxUpper lo hi η j i-boxLower lo hi η j i ≤ η i := by
  rw [boxUpper,boxLower,gridPoint_width]
  exact gridStep_le (h i) (hη i)

theorem gridCount_le_meshIntervals (r : ScaleBudget.Row) (L lo hi : ℝ)
    (hlen : hi-lo ≤ Real.exp (r.a₁*L)) :
    gridCount lo hi (meshWidth r L) ≤ meshIntervals r L := by
  exact gridCount_le_ceiling (by unfold meshWidth; positivity) hlen

theorem gridBoxIndex_card (lo hi η : ι → ℝ) :
    Fintype.card (GridBoxIndex lo hi η) = ∏ i, gridCount (lo i) (hi i) (η i) := by
  rw [Fintype.card_pi]
  simp

theorem gridBoxIndex_card_le_mesh_power (r : ScaleBudget.Row) (L : ℝ) (lo hi : ι → ℝ)
    (hlen : ∀ i, hi i-lo i ≤ Real.exp (r.a₁*L)) :
    Fintype.card (GridBoxIndex lo hi (fun _ => meshWidth r L)) ≤
      (meshIntervals r L)^(Fintype.card ι) := by
  rw [gridBoxIndex_card]
  calc
    _ ≤ ∏ _i : ι, meshIntervals r L :=
      Finset.prod_le_prod (fun i hi' => gridCount_le_meshIntervals r L (lo i) (hi i) (hlen i))
    _ = _ := by simp

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
