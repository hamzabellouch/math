import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSource
open Construction HistoryGiantReferenceMean

theorem primeMean_congr_nonneg (giant : PrimeSource) (F H : ℤ→ℤ→ℂ)
    (h : ∀P Q,0≤P → 0≤Q → F P Q=H P Q) : primeMean giant F=primeMean giant H := by
  simp only [primeMean,FinitePrior.cmean]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [h p.val q.val (by positivity) (by positivity)]

theorem mixedMean_congr_nonneg (G : ℝ) (giant : PrimeSource) (F H : ℤ→ℤ→ℂ)
    (h : ∀P Q,0≤P → 0≤Q → F P Q=H P Q) : mixedMean G giant F=mixedMean G giant H := by
  simp only [mixedMean,FinitePrior.cmean]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [h p q.val (by positivity) (by positivity)]

end Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSource

end

end OAI
