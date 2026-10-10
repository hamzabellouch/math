import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainPrincipal
import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonSpectator

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open Construction Arithmetic Filter
open HistoryBulkSourceDisintegration HistoryBulkActualTotalReplacement

theorem exists_plainFinalAverage_budget
    (d : Decomposition) (BD Bz H : ℝ) {k : ℕ} (hk : 2 ≤ k) (hH : 0 ≤ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hZ : 0 < harmonicPrimeMass P)
        (E : Finset ℕ) (C : InitialSourceChoice d 200 BD Bz k L E),
        ActualComparisonSource C P hP hZ ε →
        ∀ hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C
          (harmonicPrimeSource P hP hZ),
        ∀ (j : ℕ) (hj : j ≤ k),
        ∃ hV : SpectatorResidueBounds C (harmonicPrimeSource P hP hZ) j,
        ∀ σ, ¬TransferBadArrangement σ → ∀ mixed : Bool,
          ‖plainFinalAverage C (harmonicPrimeSource P hP hZ) hactual hj σ mixed hV‖ ≤
            Real.exp (-H*(2:ℝ)^j*(bulkSize k L:ℝ)) :=
  (HistoryBulkActualTotalReplacement.exists_plainFinalAverage_budget
    d 200 BD Bz H (Nat.cast_nonneg 200) hk hH).elim fun ε hε =>
    ⟨ε,hε.1,hε.2.mono fun _L hL P hP hZ E C hs =>
      hL E C hs.block_lower hs.block_upper hs.center_lower hs.center_upper
        hs.bulk_bin hs.spectator_bin (harmonicPrimeSource P hP hZ)
        hs.spectator_band hs.spectator_correlation_le⟩

end Ostmann.Conclusion

end

end OAI
