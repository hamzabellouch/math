import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionMean

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkFibreOriginalReference HistoryBulkReferencePeriodicMeanSource
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))

open CanonicalOccurrenceTransport CompensationEqualityPatterns HistoryPairReferenceFlagExpectation
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualRootReferenceFamily
variable {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)→SelectedBulkSample C l→ℤ→ℤ→ℂ}
  {α : Type} [Fintype α] {w : α→ℝ} {P Q : α→ℤ}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}

theorem rawBTerm_mean_eq_frameRawMean
    (R : MatchedSelectedOuter C p o outside σ J w P Q i)
    (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
      |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)
    (hp : ∀q∈outside,q.Prime) (mixed : Bool) :
    (selectedBulkPrior C l).cmean (@MatchedSelectedOuter.rawBTerm d Bs BD Bz L k l E C p o outside σ J α inferInstance w P Q i R hcell hp false mixed) =
      @frameRawMean d Bs BD Bz L k l E C outside σ (outerNonbulk C l p o) (@MatchedSelectedOuter.frame d Bs BD Bz L k l E C p o outside σ J α inferInstance w P Q i R hcell hp) mixed := rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
