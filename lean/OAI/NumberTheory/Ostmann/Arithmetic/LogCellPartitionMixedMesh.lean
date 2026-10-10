import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionMesh
import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionMixed

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open PrimeCellMeshBudget
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mixedGridIndex_card (loI hiI ηI : ℝ) (lo hi η : ι → ℝ) :
    Fintype.card (MixedGridIndex loI hiI ηI lo hi η) =
      gridCount loI hiI ηI * ∏ i, gridCount (lo i) (hi i) (η i) := by
  rw [Fintype.card_prod, Fintype.card_fin, gridBoxIndex_card]

theorem mixedGridIndex_card_le_mesh_power (r : ScaleBudget.Row) (L loI hiI : ℝ)
    (lo hi : ι → ℝ) (hI : hiI-loI ≤ Real.exp (r.a₁*L))
    (hlen : ∀ i, hi i-lo i ≤ Real.exp (r.a₁*L)) :
    Fintype.card (MixedGridIndex loI hiI (meshWidth r L) lo hi (fun _ => meshWidth r L)) ≤
      (meshIntervals r L)^(Fintype.card ι+1) := by
  rw [Fintype.card_prod, Fintype.card_fin]
  calc
    _ ≤ meshIntervals r L * (meshIntervals r L)^(Fintype.card ι) :=
      Nat.mul_le_mul (gridCount_le_meshIntervals r L loI hiI hI)
        (gridBoxIndex_card_le_mesh_power r L lo hi hlen)
    _ = _ := by rw [pow_succ, Nat.mul_comm]

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
