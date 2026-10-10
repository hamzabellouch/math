import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonProviders

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalComparison
open Construction Conclusion Filter

def ActualUniversalEstimates (d : Decomposition) (BD Bz : ℝ) (k : ℕ) : Prop :=
    ∀ᶠ L : ℝ in atTop,
    ∀(P : Finset ℕ)(hP : ∀p∈P,p.Prime)(hZ : 0<harmonicPrimeMass P)
      (E : Finset ℕ)(C : InitialSourceChoice d 200 BD Bz k L E),
    ActualComparisonSource C P hP hZ 1 →
    ∀(l : ℕ)(_hl : l≤k),
      C.selectedDiagonalSingleEnergy (harmonicPrimeSource P hP hZ)
        (bulkSize k L/2) C.scale l ≤
        Real.exp ((2:ℝ)^l*(initialGap 200 k L+17*(bulkSize k L:ℝ))) ∧
      ∀σ τ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))),
        selectedCovariance C (harmonicPrimeSource P hP hZ) (bulkSize k L/2) l σ τ ≤
          Real.exp ((2:ℝ)^l*(initialGap 200 k L+17*(bulkSize k L:ℝ)))

end Ostmann.Arithmetic.HistoryBulkActualUniversalComparison

end

end OAI
