import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMeanDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement
open Construction Conclusion HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryBulkFibreGiantApproximationReference
open HistoryGiantReferenceMean HistoryRepresentativeSourceSeparation
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)

variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hp : ∀q∈outside,q.Prime)
  (hAd : ∀r : Frame (l:=l) C outside, PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

variable (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j))
include hfreq

theorem rawPrimeSourceMean_eq_primeSourceMean :
    rawSourceMean (l:=l) C outside σ (primeLawMultiplier (l:=l) C)
      (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) hactual hl houtside
      (primeWeight_nonneg C.giant) (fun r _=>primeDraw_positive C.giant r)
      (fun r hr=>prime_draw_cells C r
        (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
      hp false false = primeSourceMean C outside σ hactual hl houtside hp hAd hout hV false :=
  rawSourceMean_eq_sourceMean (l:=l) C outside σ (primeLawMultiplier (l:=l) C)
    (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) hactual hl houtside
    (primeWeight_nonneg C.giant) (fun r _=>primeDraw_positive C.giant r)
    (fun r hr=>prime_draw_cells C r
      (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
    hp hAd hout hV hfreq false false (Or.inl rfl)

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI
