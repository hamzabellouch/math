import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReferenceBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximationReference
open HistoryGiantReferenceMean
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (outside : List ℕ) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p →
    Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hlen : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
  (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)

def primeKernelMean (symbolic : Bool) : ℂ :=
  selectedKernelMean C p outside σ J (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
    hactual hl houtside (primeWeight_nonneg C.giant)
    (fun r _ => primeDraw_positive C.giant r)
    (fun r hr => prime_draw_cells C r
      (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
    hlen hprime hV v f g symbolic false false

def mixedKernelMean (symbolic : Bool) : ℂ :=
  selectedKernelMean C p outside σ J (mixedWeight C.giantCenter C.giant)
    (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant)
    hactual hl houtside (mixedWeight_nonneg C.giantCenter C.giant)
    (fun r _ => mixedDraw_positive C.giantCenter C.giant r)
    (fun r hr => mixed_draw_cells C r
      (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
    hlen hprime hV v f g symbolic false true

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end

end OAI
