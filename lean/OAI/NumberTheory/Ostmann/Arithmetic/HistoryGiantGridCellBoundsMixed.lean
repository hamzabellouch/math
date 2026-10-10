import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantGridCellBoundsPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightDerivConstants
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellActualErrorBudgetMixed

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantGridCellBounds
open Construction Conclusion ScaleBudget Filter PrimeCellMeshBudget
open PrimeCellActualErrorBudget LogCellPartition PrimeProgression HistoryGiantReplacementGeometry

def giantMixedError (K δ G L : ℝ) (E : Finset ℕ) : ℝ :=
  2*(6+2*partitionDerivativeConstant)*Real.exp (-Real.exp (giant.a₀*L))+
    2*(Real.exp 1+6+2*partitionDerivativeConstant)*giantPrimeError K δ G E

theorem giantMixedError_nonneg {K δ G L : ℝ} {E : Finset ℕ}
    (hε : 0 ≤ giantPrimeError K δ G E) : 0 ≤ giantMixedError K δ G L E := by
  unfold giantMixedError
  have hD := partitionDerivativeConstant_pos.le
  positivity

theorem mixedGridError_le_giantMixedError {k : ℕ} {δ K L₀ G L : ℝ} {M : ℕ} {E : Finset ℕ}
    (hb : PrimeBounds k δ K L₀ G L M E) (hM : 0 < M)
    (hgeo : GeometryBounds δ L₀ G M L)
    (j : Fin (gridCount (G-1) (G+1) (meshWidth giant L))) :
    mixedGridError (ι:=Unit) M (G-1) (G+1) (meshWidth giant L) G 1
      partitionDerivativeConstant smoothPartition (giantPrimeError K δ G E) 2 j ≤
      giantMixedError K δ G L E := by
  have hG : Real.exp (giant.a₀*L) ≤ G := by linarith [hgeo.lower_scale]
  have hs := mixedGridError_le_two_parts (ι:=Unit) M hM smoothPartition j
    (by linarith : G-1 ≤ G+1) hb.mesh_pos hb.mesh_le_one (by norm_num : (0 : ℝ) ≤ 1)
    partitionDerivativeConstant_pos.le le_rfl hG
    (fun t _ => by rw [abs_of_nonneg (smoothPartition_nonneg _)]; exact smoothPartition_le_one _)
    hb.error_nonneg
  simp only [Fintype.card_unique,Nat.cast_one,pow_one,mul_one] at hs
  convert hs using 1
  unfold giantMixedError
  ring

end Ostmann.Arithmetic.HistoryGiantGridCellBounds

end

end OAI
