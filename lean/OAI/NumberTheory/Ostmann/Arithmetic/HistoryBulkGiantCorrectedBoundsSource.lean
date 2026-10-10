import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeBoundsAmplitude
import OAI.NumberTheory.Ostmann.Construction.LevelZeroFrequencySupport

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryProductWindows HistoryBulkIntegralReplacement
open HistorySelectedPairDerivativeBounds HistorySelectedPairDerivativeCounts
open HistoryBulkCorrectedXiBounds PrimeCellFreezing
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}

theorem giant_sourceDomains
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (h k : History l)
    (hsrc₁ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (hsrc₂ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    {κ : Type*} (eG : κ ≃ giantCoordinates h k) (z : κ → ℝ)
    (hz : z ∈ logRectangle (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1)) :
    let background := insert (giantCoordinates h k) (pairBackground h k)
      (fun j => Real.exp (z (eG.symm j)))
    SourceDomain (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (fun i => background (leftMap h k i)) ∧
    SourceDomain (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (fun i => background (rightMap h k i)) := by
  have hm : (fun j => z (eG.symm j)) ∈
      logRectangle (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1) :=
    fun j _ => hz (eG.symm j) (Set.mem_univ _)
  exact ⟨hsrc₁.sourceDomain _ hm,hsrc₂.sourceDomain _ hm⟩

theorem corrected_bulkBounds
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (hBs : 0 ≤ Bs) (hk₀ : 0 < k₀)
    (hm : 1 ≤ bulkSize k₀ L) (s : ℕ) {outside : List ℕ}
    (houtside : ∀ q ∈ outside, 0 < q) (hout : outside.length = 2*s)
    (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside) (hl : l < k₀)
    (hh : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h)
    (hk : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (matchRoots : RootMatching h k)
    (hsrc₁ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (hsrc₂ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (z : κ → ℝ)
    (hz : z ∈ logRectangle (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1)) :
    BulkBounds k₀ L (selectedExponent Bs BD Bz k₀)
      (jointCorrectedScalar C s h k hs ks eG eB (fun i => Real.exp (z i))) := by
  have hX : 0 < (C.scale:ℝ) := by exact_mod_cast InitialEta.initial_scale_pos C
  have hsource := giant_sourceDomains C h k hsrc₁ hsrc₂ eG z hz
  have hr := selected_bulk_corrected_bounds C s C.scale (initialGap Bs k₀ L) (2+2*(k₀:ℝ))
    hX houtside hout h k hs ks hl hh hk matchRoots _ hsource.1 hsource.2
    (selected_Xi_source_center C)
    (Finset.univ : Finset (Fin (diagonalCellKeys k (l+1)).length))
    (pairedDiagonalCellCenter k (l+1) C.giantCenter (C.cells.center (bulkSize k₀ L/2)))
    (pairedDiagonalCellKey h k (l+1)) eB
  have hcount := diagonal_cells_card_le hk hl.le (l+1)
  have hc : (Finset.univ : Finset (Fin (diagonalCellKeys k (l+1)).length)).card ≤
      (k₀+1)*countCoefficient k₀*(bulkSize k₀ L/2+1) := by
    nlinarith [Nat.zero_le (countCoefficient k₀*(bulkSize k₀ L/2+1))]
  have hD := selected_bulk_corrected_bound C hBs hk₀ hm hl.le h k hh hk (l+1) hc
  have hA := selected_amplitude_bound Bs BD Bz L hBs hk₀ hl.le
  have hA' : Real.exp ((nominalInheritedWidth k₀ l+1)+nominalRemovedWidth k₀ l)*
      Real.exp (-((2^l:ℕ):ℝ)*initialGap Bs k₀ L+sourceXiConstant l k₀ (2+2*(k₀:ℝ))) ≤
      Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) := by
    apply le_trans _ hA
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Real.exp_nonneg _)
  refine ⟨?_,?_,?_⟩
  · intro y hy
    exact hr.1.differentiable (by simp) y
  · intro y hy i
    exact (hr.2.1 _ (fun i => Real.exp_pos _) i).trans hD
  · intro y hy
    exact (hr.2.2 _ (fun i => Real.exp_pos _)).trans hA'

end Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds

end

end OAI
