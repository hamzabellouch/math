import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude

namespace OAI

namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex
open Construction

theorem spectatorList_length_eq (spectator : PrimeSource) {m : ℕ}
    (ds : Fin m → spectator.Sample) : (spectatorList spectator ds).length=m := by
  simp only [spectatorList,List.length_ofFn]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex

end OAI
