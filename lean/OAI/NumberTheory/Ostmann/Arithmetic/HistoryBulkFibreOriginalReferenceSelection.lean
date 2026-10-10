import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
open Construction Conclusion HistoryGiantReferenceMean HistoryBulkSourceDisintegration
open HistoryGiantOriginalMeanFactorization (Choices)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l) (s t : ℤ) (c e : Choices (l:=l) C)

theorem weightedFibreMean_eq_zero_or_reference
    {α : Type*} [Fintype α] (w : α → ℝ) (P Q : α → ℤ) (hw : ∀r,0≤w r) :
    HistoryBulkFibreReference.originalMean (selectedBulkPrior C l).mass w
      (fun y r => fibreTerm C outside σ a s t c e y (P r) (Q r)) = 0 ∨
    ∃y r,0<(selectedBulkPrior C l).mass y ∧ 0<w r ∧
      fibreTerm C outside σ a s t c e y (P r) (Q r) ≠ 0 ∧
      FibreSupported C outside σ a s t c e y (P r) (Q r) :=
  HistoryBulkFibreReference.originalMean_eq_zero_or_reference _ _ _
    (selectedBulkPrior C l).mass_nonneg hw
    (fun y r => FibreSupported C outside σ a s t c e y (P r) (Q r))
    (fun y r _ _ h => fibreTerm_ne_zero_supported C outside σ a s t c e y (P r) (Q r) h)

theorem weightedFibreMean_eq_zero_or_fixed_reference
    {α : Type*} [Fintype α] (w : α → ℝ) (P Q : α → ℤ) (hw : ∀r,0≤w r)
    (T : SelectedBulkSample C l → α → SelectedBulkSample C l → α → ℂ)
    (hconverse : ∀y₀ r₀,FibreSupported C outside σ a s t c e y₀ (P r₀) (Q r₀) →
      ∀y r,(selectedBulkPrior C l).mass y ≠ 0 → w r ≠ 0 → T y₀ r₀ y r ≠ 0 →
        FibreSupported C outside σ a s t c e y (P r) (Q r))
    (htransport : ∀y₀ r₀,FibreSupported C outside σ a s t c e y₀ (P r₀) (Q r₀) →
      ∀y r,(selectedBulkPrior C l).mass y ≠ 0 → w r ≠ 0 →
        FibreSupported C outside σ a s t c e y (P r) (Q r) →
        fibreTerm C outside σ a s t c e y (P r) (Q r) = T y₀ r₀ y r) :
    HistoryBulkFibreReference.originalMean (selectedBulkPrior C l).mass w
      (fun y r => fibreTerm C outside σ a s t c e y (P r) (Q r)) = 0 ∨
    ∃y₀ r₀,0<(selectedBulkPrior C l).mass y₀ ∧ 0<w r₀ ∧
      fibreTerm C outside σ a s t c e y₀ (P r₀) (Q r₀) ≠ 0 ∧
      FibreSupported C outside σ a s t c e y₀ (P r₀) (Q r₀) ∧
      (∀y r,(selectedBulkPrior C l).mass y ≠ 0 → w r ≠ 0 →
        fibreTerm C outside σ a s t c e y (P r) (Q r) = T y₀ r₀ y r) ∧
      HistoryBulkFibreReference.originalMean (selectedBulkPrior C l).mass w
        (fun y r => fibreTerm C outside σ a s t c e y (P r) (Q r)) =
      HistoryBulkFibreReference.originalMean (selectedBulkPrior C l).mass w (T y₀ r₀) :=
  HistoryBulkFibreReference.originalMean_eq_zero_or_fixed_reference _ _ _
    (selectedBulkPrior C l).mass_nonneg hw
    (fun y r => FibreSupported C outside σ a s t c e y (P r) (Q r)) T
    (fun y r _ _ h => fibreTerm_ne_zero_supported C outside σ a s t c e y (P r) (Q r) h)
    hconverse htransport

end Ostmann.Arithmetic.HistoryBulkFibreOriginalReference

end

end OAI
