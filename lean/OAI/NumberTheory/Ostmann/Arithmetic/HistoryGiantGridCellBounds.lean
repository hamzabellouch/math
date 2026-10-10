import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantGridCellBoundsBudget

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantGridCellBounds
open Construction Conclusion ScaleBudget Filter PrimeCellMeshBudget
open PrimeCellActualErrorBudget LogCellPartition PrimeProgression HistoryGiantReplacementGeometry

theorem selected_gridCellBounds_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) (L₀ : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10 : ℝ)*L) →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ M : ℕ, 0 < M → Real.log (M : ℝ) ≤ Real.exp (giant.μ*L) →
      GeometryBounds δ L₀ C.giantCenter M L ∧
      ∀ deleted : Finset ℕ, deleted.card ≤ 2 →
        PrimeBounds k δ K L₀ C.giantCenter L M deleted ∧
        0 ≤ giantMixedError K δ C.giantCenter L deleted ∧
        ∀ j : Fin (gridCount (C.giantCenter-1) (C.giantCenter+1) (meshWidth giant L)),
          mixedGridError (ι:=Unit) M (C.giantCenter-1) (C.giantCenter+1) (meshWidth giant L)
            C.giantCenter 1 partitionDerivativeConstant smoothPartition
            (giantPrimeError K δ C.giantCenter deleted) 2 j ≤
            giantMixedError K δ C.giantCenter L deleted := by
  filter_upwards [eventually_primeBounds hk hK hδ L₀,
    RepeatedPriorBounds.initial_cell_centers_eventually d Bs BD Bz hk,
    HistoryGiantReplacementGeometry.eventually_geometryBounds hδ L₀] with L hb hc hg
  intro E C hG hGu hcl hcu hbulk houtside M hM hmod
  have hgeo := hg C.blockBase C.giantCenter M hG hcl hM hmod
  refine ⟨hgeo,?_⟩
  intro deleted hdeleted
  have hprime := hb C.giantCenter M deleted hM hgeo
    (hc E C hG hGu hcl hcu hbulk houtside).1.2 hdeleted
  exact ⟨hprime,giantMixedError_nonneg hprime.error_nonneg,
    fun j => mixedGridError_le_giantMixedError hprime hM hgeo j⟩

end Ostmann.Arithmetic.HistoryGiantGridCellBounds

end

end OAI
