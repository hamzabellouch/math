import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantGridCellBoundsMonotone
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantGridCellBoundsNormalization
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReplacementErrorBasic
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellActualErrorBudgetMass

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantGridCellBounds
open Construction Conclusion ScaleBudget Filter PrimeCellMeshBudget
open PrimeCellActualErrorBudget LogCellPartition PrimeProgression HistoryGiantReplacementGeometry

def giantPrimeError (K δ G : ℝ) (E : Finset ℕ) : ℝ :=
  correctedPrimeError K δ (G-1) (Construction.logCellMass G E)

structure PrimeBounds (k : ℕ) (δ K L₀ G L : ℝ) (M : ℕ) (E : Finset ℕ) : Prop where
  mass_pos : 0 < Construction.logCellMass G E
  inverse_mass : (Construction.logCellMass G E)⁻¹ ≤ 2*G
  inverse_cost : (Construction.logCellMass G E)⁻¹ ≤ Real.exp (2*((bulkSize k L : ℝ)+1))
  mesh_pos : 0 < meshWidth giant L
  mesh_le_one : meshWidth giant L ≤ 1
  error_nonneg : 0 ≤ giantPrimeError K δ G E
  error_le_envelope : giantPrimeError K δ G E ≤ primeEnvelope giant k 2 K δ L
  boxes : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (j : GridBoxIndex (fun _ : ι => G-1) (fun _ => G+1) (fun _ => meshWidth giant L)) (i : ι),
    let lower := boxLower (fun _ => G-1) (fun _ => G+1) (fun _ => meshWidth giant L) j i
    let upper := boxUpper (fun _ => G-1) (fun _ => G+1) (fun _ => meshWidth giant L) j i
    L₀ ≤ lower ∧ (M : ℝ) < Real.exp lower ∧ (M : ℝ) ≤ Real.exp (δ*lower^(1/3 : ℝ)) ∧
    correctedPrimeError K δ lower (Construction.logCellMass G E) ≤ giantPrimeError K δ G E ∧
    |harmonicIntegral M lower upper/Construction.logCellMass G E|+giantPrimeError K δ G E ≤ 2

theorem eventually_primeBounds {k : ℕ} (hk : 0 < k) {K δ : ℝ}
    (hK : 0 ≤ K) (hδ : 0 < δ) (L₀ : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (G : ℝ) (M : ℕ) (E : Finset ℕ),
      0 < M → GeometryBounds δ L₀ G M L → G ≤ Real.exp L/2 → E.card ≤ 2 →
      PrimeBounds k δ K L₀ G L M E := by
  filter_upwards [eventually_giant_normalization hk,
    eventually_actual_primeCell_bounds giant k (by norm_num : (0 : ℝ) ≤ 2) hK hδ,
    eventually_ge_atTop (0 : ℝ)] with L hn hb hL
  intro G M E hM hgeo hGu hE
  obtain ⟨hZ,hZi,hcost⟩ := hn G E hgeo.lower_scale hGu hE
  have hη : 0 < meshWidth giant L := Real.exp_pos _
  have he : giantPrimeError K δ G E ≤ primeEnvelope giant k 2 K δ L :=
    correctedPrimeError_le_envelope giant k hK hδ hL hgeo.lower_scale hZ hcost
  refine ⟨hZ,hZi,hcost,hη,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_nonneg _)),
    HistoryGiantReplacementError.correctedPrimeError_nonneg hK hZ,he,?_⟩
  intro ι _ _ j i
  dsimp only
  have horder (i : ι) : G-1 ≤ G+1 := by linarith
  have hlo := boxLower_ge _ _ _ horder j i
  have hlocal := hgeo.at_lower hδ.le hlo
  have hw := box_width_le _ _ _ horder (fun _ => hη) j i
  have hh := hb M _ _ (Construction.logCellMass G E) hM hlocal.1
    (box_order _ _ _ horder j i) hw hZ hcost
  refine ⟨hlocal.2.2.1,hlocal.2.1,hlocal.2.2.2,?_,?_⟩
  · exact correctedPrimeError_antitone_lower hK hδ.le hZ
      ((Real.exp_pos _).le.trans hgeo.lower_scale) hlo
  · exact (add_le_add le_rfl he).trans hh.2

end Ostmann.Arithmetic.HistoryGiantGridCellBounds

end

end OAI
