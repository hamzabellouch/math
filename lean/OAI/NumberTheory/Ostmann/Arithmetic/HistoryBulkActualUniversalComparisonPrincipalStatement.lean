import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainDefs
import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonProviders

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalComparison
open Construction Conclusion Filter HistoryBulkActualTotalReplacement HistoryBulkSourceDisintegration

def ActualPlainFinalEstimate (d : Decomposition) (BD Bz : ℝ) (k : ℕ) : Prop :=
    ∀ᶠ L : ℝ in atTop,
    ∀(P : Finset ℕ)(hP : ∀p∈P,p.Prime)(hZ : 0<harmonicPrimeMass P)
      (E : Finset ℕ)(C : InitialSourceChoice d 200 BD Bz k L E),
    ActualComparisonSource C P hP hZ 1 →
    ∃hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C (harmonicPrimeSource P hP hZ),
    ∀(l : ℕ)(hl : l≤k),∃hV : SpectatorResidueBounds C (harmonicPrimeSource P hP hZ) l,
    ∀mixed : Bool,
      ‖plainFinalAverage (d:=d) (Bs:=200) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C (harmonicPrimeSource P hP hZ) hactual hl
        (Equiv.refl (Fin (2^l) × Fin (2*(bulkSize k L/2)))) mixed hV‖ ≤
        Real.exp ((2:ℝ)^l*(initialGap 200 k L+16*(bulkSize k L:ℝ)))

end Ostmann.Arithmetic.HistoryBulkActualUniversalComparison

end

end OAI
