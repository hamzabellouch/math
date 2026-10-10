import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPrincipalMassBoundsOriginal
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorExceptionalError
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReplacementErrorPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualErrorAlgebra
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualErrorDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesComparisonNorm
import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionMixed
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellMeshCounts

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementActual
open Construction Conclusion HistoryPairSmoothXi HistoryProductWindows
open HistorySymbolicEncoding HistorySelectedPairDerivativeBounds HistorySelectedPairDerivativeCounts
open ScaleBudget PrimeCellMeshBudget PrimeCellActualErrorBudget LogCellPartition

lemma referenceAmplitude_nonneg (Bs L : ℝ) (k₀ l : ℕ) :
    0 ≤ referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l := by
  unfold referenceAmplitude
  positivity

lemma referenceDerivative_nonneg {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (h k : History l) (cells : List Bool) :
    0 ≤ referenceDerivative C h k cells := by
  apply correctedPairDerivativeBound_nonneg

lemma selected_exp_le_smoothGrowth (Bs BD Bz L : ℝ) (k₀ : ℕ) :
    Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L : ℝ)+1)) ≤
      smoothGrowthFactor k₀ (selectedExponent Bs BD Bz k₀) giant.μ L := by
  apply Real.exp_le_exp.mpr
  have hp := selectedExponent_pos Bs BD Bz k₀
  nlinarith [Real.exp_nonneg (giant.μ*L),
    mul_nonneg (mul_nonneg hp.le (show 0 ≤ (bulkSize k₀ L : ℝ)+1 by positivity))
      (Real.exp_nonneg (giant.μ*L))]

theorem reference_envelopes {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (hBs : 0 ≤ Bs) (hk : 0 < k₀)
    (hm : 1 ≤ bulkSize k₀ L) (hl : l ≤ k₀) (h k : History l)
    (hh : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h)
    (hk' : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (cells : List Bool) (hc : cells.length ≤ 2) :
    referenceDerivative C h k cells ≤ smoothGrowthFactor k₀ (selectedExponent Bs BD Bz k₀) giant.μ L ∧
    referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l ≤
      smoothGrowthFactor k₀ (selectedExponent Bs BD Bz k₀) giant.μ L := by
  have hcount := diagonal_prior_cells_card_le hk' hl (l+1) cells hc
  simp only [Finset.card_univ] at hcount
  have hcount' : Fintype.card (Fin (diagonalCellKeys k (l+1)).length ⊕ Fin cells.length) ≤
      (k₀+1)*countCoefficient k₀*(bulkSize k₀ L/2+1) := by
    apply hcount.trans
    nlinarith [Nat.zero_le (k₀*(countCoefficient k₀*(bulkSize k₀ L/2+1)))]
  exact ⟨(selected_corrected_bound C hBs hk hm hl h k hh hk' (l+1) hcount').trans
    (selected_exp_le_smoothGrowth Bs BD Bz L k₀),
    (selected_amplitude_bound Bs BD Bz L hBs hk hl).trans
      (selected_exp_le_smoothGrowth Bs BD Bz L k₀)⟩

lemma prime_grid_card_le (G L : ℝ) (hlen : 2 ≤ Real.exp (giant.a₁*L)) :
    (Fintype.card (GridBoxIndex (fun _ : Bool => G-1) (fun _ => G+1)
      (fun _ => meshWidth giant L)) : ℝ) ≤ (meshIntervals giant L : ℝ)^2 := by
  have hcount : gridCount (G-1) (G+1) (meshWidth giant L) ≤ meshIntervals giant L :=
    gridCount_le_ceiling (by unfold meshWidth; positivity) (by linarith)
  change (Fintype.card (Bool → Fin (gridCount (G-1) (G+1) (meshWidth giant L))) : ℝ) ≤ _
  rw [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  exact_mod_cast Nat.pow_le_pow_left hcount 2

lemma mixed_grid_card_le (G L : ℝ) (hlen : 2 ≤ Real.exp (giant.a₁*L)) :
    (Fintype.card (MixedGridIndex (G-1) (G+1) (meshWidth giant L)
      (fun _ : Unit => G-1) (fun _ => G+1) (fun _ => meshWidth giant L)) : ℝ) ≤
      (meshIntervals giant L : ℝ)^2 := by
  simpa only [MixedGridIndex,GridBoxIndex,Fintype.card_prod,Fintype.card_fun,
    Fintype.card_fin,Fintype.card_unique,Fintype.card_bool,pow_one,← pow_two]
    using prime_grid_card_le G L hlen

end Ostmann.Arithmetic.HistoryGiantXiReplacementActual

end

end OAI
