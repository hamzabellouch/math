import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferencePermutation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryGiantOriginalMeanFactorization (Choices choicesPairSum)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

theorem bulk_primeMean_relative (outside : List ℕ)
    (σ τ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (a : SelectedNonbulkSample C l) (s t : ℤ) (c e : Choices (l:=l) C) :
    (selectedBulkPrior C l).cmean (fun y =>
      HistoryGiantUncorrectedOriginalMean.originalPrimeMean C outside
        (permuteAssignment C σ (fibreAssignment C a y))
        (permuteAssignment C τ (fibreAssignment C a y)) s t c e) =
      primeFibreMean C outside (σ⁻¹*τ) a s t c e := by
  change _ = (selectedBulkPrior C l).cmean (fun y =>
    HistoryGiantUncorrectedOriginalMean.originalPrimeMean C outside (fibreAssignment C a y)
      (permuteAssignment C (σ⁻¹*τ) (fibreAssignment C a y)) s t c e)
  simp_rw [permute_fibreAssignment]
  exact bulk_cmean_relative_permutation C σ τ
    (fun y z => HistoryGiantUncorrectedOriginalMean.originalPrimeMean C outside
      (fibreAssignment C a y) (fibreAssignment C a z) s t c e)

theorem selectedComplexCovariance_eq_fibres (spectator : PrimeSource)
    (σ τ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) :
    selectedComplexCovariance C spectator (bulkSize k L/2) l σ τ =
      (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds =>
        (selectedNonbulkPrior C l).cmean (fun a =>
          ∑v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
            choicesPairSum C (fun c e =>
              primeFibreMean C (spectatorList spectator ds) (σ⁻¹*τ) a v.val v.val c e))) := by
  rw [HistoryGiantUncorrectedOriginalMean.selectedComplexCovariance_eq_originalMean]
  apply congrArg (FinitePrior.cmean (spectatorPrior spectator (2*(bulkSize k L/2))))
  funext ds
  rw [selected_source_cmean_disintegration]
  apply congrArg (FinitePrior.cmean (selectedNonbulkPrior C l))
  funext a
  simp only [choicesPairSum]
  rw [cmean_frequency_choices]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e _
  exact congrArg (fun z : ℂ =>
    ((choicesMass C.sources _ _ l c * choicesMass C.sources _ _ l e : ℝ):ℂ) * z)
    (bulk_primeMean_relative C (spectatorList spectator ds) σ τ a v.val v.val c e)

theorem selectedCovariance_eq_fibres (spectator : PrimeSource)
    (σ τ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) :
    selectedCovariance C spectator (bulkSize k L/2) l σ τ =
      ((spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds =>
        (selectedNonbulkPrior C l).cmean (fun a =>
          ∑v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
            choicesPairSum C (fun c e =>
              primeFibreMean C (spectatorList spectator ds) (σ⁻¹*τ) a v.val v.val c e)))).re := by
  rw [←selectedComplexCovariance_re,selectedComplexCovariance_eq_fibres]

end Ostmann.Arithmetic.HistoryBulkFibreOriginalReference

end

end OAI
