import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionSelectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSelectedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkActualRootReferenceFamily HistoryBulkActualPrincipalBlockFamily
open HistoryBulkPrincipalCollisionError HistoryPairSourceLaws
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximationReference
open HistoryBulkFibreGiantApproximation HistoryGiantReferenceMean
open HistoryBulkFibreGiantErrorAverage HistoryBulkFibreOriginalReference
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q)

def plainMixedReferences (bg : Background C l)
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) :
    ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
    (Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) →
    Option (PrincipalCollisionReference C (spectatorList spectator ds) bg.2 p) :=
selectedCollisionReferences (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (α:=MixedDraw C.giantCenter C.giant) (spectator:=spectator)
      C (spectatorList spectator ds) σ
      (fun (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) =>
        plainMixedWeight C (spectatorList spectator ds) bg.2 i.1.val)
      (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant)
      hactual hl (HistoryBulkFibreGiantErrorAverage.spectatorList_source spectator ds) (mixedWeight_nonneg C.giantCenter C.giant)
      (fun r _=>mixedDraw_positive C.giantCenter C.giant r)
      (fun r hr=>mixed_draw_cells C r (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
      List.length_ofFn (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
      hV bg i

def plainMixedMask (bg : Background C l)
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) :
    SelectedBulkSample C l → ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
    (Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → ℝ :=
selectedCollisionMask (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (α:=MixedDraw C.giantCenter C.giant) (spectator:=spectator)
      C (spectatorList spectator ds) σ
      (fun (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) =>
        plainMixedWeight C (spectatorList spectator ds) bg.2 i.1.val)
      (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant)
      hactual hl (HistoryBulkFibreGiantErrorAverage.spectatorList_source spectator ds) (mixedWeight_nonneg C.giantCenter C.giant)
      (fun r _=>mixedDraw_positive C.giantCenter C.giant r)
      (fun r hr=>mixed_draw_cells C r (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) bg i true

theorem plainMixedMask_mem (bg : Background C l)
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
    (u : SelectedBulkSample C l) (p) (b) :
    0 ≤ plainMixedMask C spectator ds hactual hl σ bg i u p b ∧
    plainMixedMask C spectator ds hactual hl σ bg i u p b ≤ 1 :=
  selectedCollisionMask_mem (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
    (k:=k) (l:=l) (E:=E) (α:=MixedDraw C.giantCenter C.giant) (spectator:=spectator)
    C (spectatorList spectator ds) σ
    (fun (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) =>
        plainMixedWeight C (spectatorList spectator ds) bg.2 i.1.val)
    (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant)
    hactual hl (spectatorList_source spectator ds) (mixedWeight_nonneg C.giantCenter C.giant)
    (fun r _=>mixedDraw_positive C.giantCenter C.giant r)
    (fun r hr=>mixed_draw_cells C r (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) bg i true u p b

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
