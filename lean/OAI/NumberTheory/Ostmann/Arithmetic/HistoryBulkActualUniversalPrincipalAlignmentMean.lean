import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalPlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignment
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalSelectedReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion HistoryBulkSourceDisintegration
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l ≤ k)
  (hout : ∀ ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
    ∀ q ∈ spectatorList spectator ds, q ∈ spectator.candidates)
  (mixed : Bool)
  (hV : ∀ ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
    ∀ q ∈ spectatorList spectator ds, ∀ j ≤ l, frequencyBound Bs BD Bz k L j < q)

theorem replacementMean_eq_plainPrincipalMean :
    (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds =>
      HistoryBulkPatternIntegralReplacement.backgroundValue true
        (fun background pattern diagonal =>
          selectedReplacementBackground C (spectatorList spectator ds) hactual hl (hout ds)
            background pattern diagonal mixed)
        false mixed (hV ds)) =
      (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds =>
        HistoryBulkActualGoodPrincipal.plainPrincipal (l:=l) C spectator ds hactual hl
          (Equiv.refl (Fin (2^l) × Fin (2*(bulkSize k L/2)))) mixed (hV ds)) :=
  congrArg ((spectatorPrior spectator (2*(bulkSize k L/2))).cmean)
    (funext fun ds =>
      replacementBackground_eq_plainPrincipal
        (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C spectator ds hactual hl (hout ds) mixed (hV ds))

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
