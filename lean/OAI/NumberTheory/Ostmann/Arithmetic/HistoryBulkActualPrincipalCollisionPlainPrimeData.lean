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

def plainPrimeReferences (bg : Background C l)
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) :
    ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
    (Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) →
    Option (PrincipalCollisionReference C (spectatorList spectator ds) bg.2 p) :=
selectedCollisionReferences (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (α:=PrimeDraw C.giant) (spectator:=spectator)
      C (spectatorList spectator ds) σ
      (fun (_ : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) _ _ _=>1)
      (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
      hactual hl (HistoryBulkFibreGiantErrorAverage.spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
      (fun r _=>primeDraw_positive C.giant r)
      (fun r hr=>prime_draw_cells C r (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
      List.length_ofFn (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
      hV bg i

def plainPrimeMask (bg : Background C l)
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) :
    SelectedBulkSample C l → ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
    (Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → ℝ :=
selectedCollisionMask (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (α:=PrimeDraw C.giant) (spectator:=spectator)
      C (spectatorList spectator ds) σ
      (fun (_ : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) _ _ _=>1)
      (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
      hactual hl (HistoryBulkFibreGiantErrorAverage.spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
      (fun r _=>primeDraw_positive C.giant r)
      (fun r hr=>prime_draw_cells C r (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) bg i false

theorem plainPrimeMask_mem (bg : Background C l)
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
    (u : SelectedBulkSample C l) (p) (b) :
    0 ≤ plainPrimeMask C spectator ds hactual hl σ bg i u p b ∧
    plainPrimeMask C spectator ds hactual hl σ bg i u p b ≤ 1 :=
  selectedCollisionMask_mem (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
    (k:=k) (l:=l) (E:=E) (α:=PrimeDraw C.giant) (spectator:=spectator)
    C (spectatorList spectator ds) σ
    (fun (_ : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) _ _ _=>1)
    (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
    hactual hl (spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
    (fun r _=>primeDraw_positive C.giant r)
    (fun r hr=>prime_draw_cells C r (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) bg i false u p b

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
