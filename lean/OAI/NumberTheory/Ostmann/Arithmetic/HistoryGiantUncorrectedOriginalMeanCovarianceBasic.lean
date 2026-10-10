import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMeanCovarianceFinite

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMean
open Construction Conclusion HistorySignedXiTransport HistoryGiantReferenceMean
open HistoryGiantOriginalMeanFactorization (Seed Current Choices)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem selectedCovarianceXiTerm_primeMean
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (σ τ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample)
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) (c e : Choices (l:=l) C) :
    C.giant.law.cmean (fun p => C.giant.law.cmean (fun q =>
      C.selectedCovarianceXiTerm spectator (bulkSize k L/2) l σ τ ds (p,q,x) v c e)) =
    originalPrimeMean C (spectatorList spectator ds)
      (sourceAssignmentPermutation C.sources (Current (k:=k) (L:=L) (l:=l))
        (selectedLeafPermutation C l σ) (selectedLeafPermutation_source C l σ) x)
      (sourceAssignmentPermutation C.sources (Current (k:=k) (L:=L) (l:=l))
        (selectedLeafPermutation C l τ) (selectedLeafPermutation_source C l τ) x)
      v.val v.val c e := by
  simp only [originalPrimeMean,primeMean,sourceIntegrand,one_mul,
    InitialSourceChoice.selectedCovarianceXiTerm,InitialSourceChoice.selectedPermutedHistory,
    InitialSourceChoice.selectedPermutedState,outerState,giantState,sourceState,Int.toNat_natCast]

end Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMean

end

end OAI
