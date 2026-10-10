import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeCells
import Mathlib.Data.Int.Interval

namespace OAI

/-! A bounded rectangle splits into uniformly many half-open cells.
Each cell has the exact center bounds used by the ordinary tree estimate. -/
noncomputable section
open Set
namespace LipschitzHilbert

def spatialCellIndex (a L x : ℝ) : ℤ := ⌊(x-a)/L⌋
def spatialCellCenter (a L : ℝ) (i : ℤ) : ℝ := a+((i:ℝ)+1/2)*L

theorem spatialCell_center_bound (a L x : ℝ) (hL : 0<L) :
    |x-spatialCellCenter a L (spatialCellIndex a L x)|≤L/2 := by
  have hlo := (le_div_iff₀ hL).mp (Int.floor_le ((x-a)/L))
  have hhi := (div_lt_iff₀ hL).mp (Int.lt_floor_add_one ((x-a)/L))
  unfold spatialCellCenter spatialCellIndex
  rw [abs_le]
  constructor <;> linarith

theorem spatialCell_index_bound (a L x : ℝ) (hL : 0<L) (K : ℕ)
    (hx : |x-a|≤(K:ℝ)*L) :
    spatialCellIndex a L x∈Finset.Icc (-(K:ℤ)) K := by
  have hlo : -(K:ℝ)≤(x-a)/L := (le_div_iff₀ hL).mpr (by linarith [(abs_le.mp hx).1])
  have hhi : (x-a)/L≤(K:ℝ) := (div_le_iff₀ hL).mpr (abs_le.mp hx).2
  apply Finset.mem_Icc.mpr
  constructor
  · apply Int.le_floor.mpr
    simpa only [Int.cast_neg,Int.cast_natCast] using hlo
  · have h := (Int.floor_le ((x-a)/L)).trans hhi
    exact_mod_cast h

/-- Cells covering an enlarged top are bounded independently of packet count. -/
theorem spatialCell_count (K : ℕ) :
    ((Finset.Icc (-(K:ℤ)) K) ×ˢ (Finset.Icc (-(K:ℤ)) K)).card=(2*K+1)^2 := by
  rw [Finset.card_product]
  have hc : (Finset.Icc (-(K:ℤ)) K).card=2*K+1 := by
    rw [Int.card_Icc]
    omega
  rw [hc]
  ring

def spatialPacketCell {ι : Type*} (x y : ι → ℝ) (a b L W : ℝ) (q : ι) : ℤ×ℤ :=
  (spatialCellIndex a L (x q),spatialCellIndex b W (y q))

theorem spatialPacketCell_mem {ι : Type*} (x y : ι → ℝ) (a b L W : ℝ)
    (hL : 0<L) (hW : 0<W) (K : ℕ) (q : ι)
    (hx : |x q-a|≤(K:ℝ)*L) (hy : |y q-b|≤(K:ℝ)*W) :
    spatialPacketCell x y a b L W q∈
      (Finset.Icc (-(K:ℤ)) K) ×ˢ (Finset.Icc (-(K:ℤ)) K) :=
  Finset.mem_product.mpr ⟨spatialCell_index_bound a L (x q) hL K hx,
    spatialCell_index_bound b W (y q) hW K hy⟩

end LipschitzHilbert

end

end OAI
