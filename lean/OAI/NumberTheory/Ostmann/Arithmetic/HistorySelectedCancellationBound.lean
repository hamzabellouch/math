import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightScale
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupportCenters

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialSourceChoice
open Filter Conclusion Arithmetic.HistorySymbolicEncoding
open Arithmetic.HistoryProductWindows InitialCoordinatesTemplate

def selectedCancellationConstant (Bs BD Bz : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * sourceScaleConstant Bs BD Bz k

theorem selectedCancellationConstant_pos (Bs BD Bz : ℝ) (k : ℕ) :
    0 < selectedCancellationConstant Bs BD Bz k := by
  exact mul_pos (by positivity) (sourceScaleConstant_pos Bs BD Bz k)

theorem selected_cancellation_center_errors
    {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) :
    |(∑ h, ∑ i, topCenters (bulkSize k L / 2)
      (C.cells.center (bulkSize k L / 2)) h i) -
      (nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin -
        2 * (C.bulkBin : ℝ))| ≤ 2 ∧
    (∀ j < k, |typeCenter (bulkSize k L / 2) j
      (C.cells.center (bulkSize k L / 2)) -
      nominalWeight k
        (nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin)
        (stepGap BD Bz k L) j| ≤ 2) := by
  exact ⟨C.top_frequency_center_error _, fun j hj => C.type_frequency_center_error _ j hj⟩

theorem selected_sourceCancellationBound_le_exp_linear
    {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (hm : 1 ≤ bulkSize k L) {l : ℕ} (hl : l ≤ k) :
    sourceCancellationBound (frequencyBound Bs BD Bz k L)
      (bulkSize k L / 2) k C.bulkBin (C.cells.center (bulkSize k L / 2)) l ≤
      Real.exp (selectedCancellationConstant Bs BD Bz k * (bulkSize k L : ℝ)) := by
  obtain ⟨htop, htypes⟩ := C.selected_cancellation_center_errors
  exact sourceCancellationBound_le_exp_linear Bs BD Bz (bulkSize k L / 2) k L C.bulkBin
    (nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin)
    (C.cells.center (bulkSize k L / 2)) hm hl htop htypes

theorem selected_sourceCancellationBound_eventually (d : Decomposition)
    (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ)
      (C : InitialSourceChoice d Bs BD Bz k L E), ∀ l ≤ k,
      sourceCancellationBound (frequencyBound Bs BD Bz k L)
        (bulkSize k L / 2) k C.bulkBin (C.cells.center (bulkSize k L / 2)) l ≤
        Real.exp (selectedCancellationConstant Bs BD Bz k * (bulkSize k L : ℝ)) := by
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop (1 : ℝ)] with L hL
  intro E C l hl
  have hm : 1 ≤ bulkSize k L := by exact_mod_cast hL
  exact C.selected_sourceCancellationBound_le_exp_linear hm hl

end Ostmann.Construction.InitialSourceChoice

end

end OAI
