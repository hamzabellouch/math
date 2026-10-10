import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceDisintegration

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

abbrev SpectatorResidueBounds (_C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (l : ℕ) : Prop :=
  ∀ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
    ∀q∈spectatorList spectator ds,∀j ≤ l,frequencyBound Bs BD Bz k L j<q

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
