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

theorem rawMixedSourceMean_eq_plainMixedSourceMean :
    rawSourceMean (l:=l) C outside σ (plainMixedLawMultiplier (l:=l) C outside)
      (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) hactual hl houtside
      (mixedWeight_nonneg C.giantCenter C.giant) (fun r _=>mixedDraw_positive C.giantCenter C.giant r)
      (fun r hr=>mixed_draw_cells C r
        (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
      hp false true = plainMixedSourceMean C outside σ hactual hl houtside hp hAd hout hV false :=
  rawSourceMean_eq_sourceMean (l:=l) C outside σ (plainMixedLawMultiplier (l:=l) C outside)
    (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) hactual hl houtside
    (mixedWeight_nonneg C.giantCenter C.giant) (fun r _=>mixedDraw_positive C.giantCenter C.giant r)
    (fun r hr=>mixed_draw_cells C r
      (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
    hp hAd hout hV hfreq false true (Or.inl rfl)

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI
