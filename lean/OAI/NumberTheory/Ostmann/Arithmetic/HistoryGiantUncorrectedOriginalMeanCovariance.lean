import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMeanCovarianceBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMean
open Construction Conclusion
open HistoryGiantOriginalMeanFactorization (Seed Current Choices choicesPairSum)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem selectedComplexCovariance_eq_originalMean
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (σ τ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) :
    selectedComplexCovariance C spectator (bulkSize k L/2) l σ τ =
      (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds =>
        (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).cmean (fun x =>
          ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
            choicesPairSum C (fun c e => originalPrimeMean C (spectatorList spectator ds)
              (sourceAssignmentPermutation C.sources (Current (k:=k) (L:=L) (l:=l))
                (selectedLeafPermutation C l σ) (selectedLeafPermutation_source C l σ) x)
              (sourceAssignmentPermutation C.sources (Current (k:=k) (L:=L) (l:=l))
                (selectedLeafPermutation C l τ) (selectedLeafPermutation_source C l τ) x)
              v.val v.val c e))) := by
  rw [C.selectedComplexCovariance_eq_historyXi]
  apply congrArg (FinitePrior.cmean (spectatorPrior spectator (2*(bulkSize k L/2))))
  funext ds
  rw [outerPrior_cmean_assignment_first]
  apply congrArg (FinitePrior.cmean (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))))
  funext x
  rw [pair_cmean_frequency_choices]
  simp_rw [selectedCovarianceXiTerm_primeMean]
  rfl

theorem selectedCovariance_eq_originalMean
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (σ τ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) :
    selectedCovariance C spectator (bulkSize k L/2) l σ τ =
      ((spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds =>
        (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).cmean (fun x =>
          ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
            choicesPairSum C (fun c e => originalPrimeMean C (spectatorList spectator ds)
              (sourceAssignmentPermutation C.sources (Current (k:=k) (L:=L) (l:=l))
                (selectedLeafPermutation C l σ) (selectedLeafPermutation_source C l σ) x)
              (sourceAssignmentPermutation C.sources (Current (k:=k) (L:=L) (l:=l))
                (selectedLeafPermutation C l τ) (selectedLeafPermutation_source C l τ) x)
              v.val v.val c e)))).re := by
  rw [←selectedComplexCovariance_re,selectedComplexCovariance_eq_originalMean]

end Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMean

end

end OAI
