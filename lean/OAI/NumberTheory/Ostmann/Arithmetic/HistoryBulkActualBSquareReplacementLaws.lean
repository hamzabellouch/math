import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMeanDefs

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

def primeLawMultiplier : Background C l →
    Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
    SelectedBulkSample C l → ℤ → ℤ → ℂ := fun _ _ _ _ _ => 1

def plainMixedLawMultiplier : Background C l →
    Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
    SelectedBulkSample C l → ℤ → ℤ → ℂ :=
  fun bg i u P Q =>
    (HistoryDiagonalSmallOriginalMean.smallMultiplier C outside
      (HistoryBulkFibreOriginalReference.fibreAssignment C bg.2 u) i.1.val P Q : ℂ)

variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hp : ∀q∈outside,q.Prime)
  (hAd : ∀r : Frame (l:=l) C outside, PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

def primeSourceMean (probability : Bool) : ℂ :=
  sourceMean C outside σ (primeLawMultiplier C)
    (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
    hactual hl houtside (primeWeight_nonneg C.giant)
    (fun r _ => primeDraw_positive C.giant r)
    (fun r hr => prime_draw_cells C r
      (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
    hp hAd hout hV probability false false

def plainMixedSourceMean (probability : Bool) : ℂ :=
  sourceMean C outside σ (plainMixedLawMultiplier C outside)
    (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant)
    (mixedQ C.giantCenter C.giant) hactual hl houtside
    (mixedWeight_nonneg C.giantCenter C.giant)
    (fun r _ => mixedDraw_positive C.giantCenter C.giant r)
    (fun r hr => mixed_draw_cells C r
      (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
    hp hAd hout hV probability false true

def primeFrequencyError : ℝ :=
  frequencyError C outside σ (primeLawMultiplier C)
    (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
    hactual hl houtside (primeWeight_nonneg C.giant)
    (fun r _ => primeDraw_positive C.giant r)
    (fun r hr => prime_draw_cells C r
      (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
    hp hAd hout hV false false

def plainMixedFrequencyError : ℝ :=
  frequencyError C outside σ (plainMixedLawMultiplier C outside)
    (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant)
    (mixedQ C.giantCenter C.giant) hactual hl houtside
    (mixedWeight_nonneg C.giantCenter C.giant)
    (fun r _ => mixedDraw_positive C.giantCenter C.giant r)
    (fun r hr => mixed_draw_cells C r
      (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
    hp hAd hout hV false true

theorem norm_primeSourceMean_sub_le :
    ‖primeSourceMean C outside σ hactual hl houtside hp hAd hout hV false -
      primeSourceMean C outside σ hactual hl houtside hp hAd hout hV true‖ ≤
      primeFrequencyError C outside σ hactual hl houtside hp hAd hout hV :=
  norm_sourceMean_sub_le_frequencyError C outside σ (primeLawMultiplier C)
    (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
    hactual hl houtside (primeWeight_nonneg C.giant)
    (fun r _ => primeDraw_positive C.giant r)
    (fun r hr => prime_draw_cells C r
      (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
    hp hAd hout hV false false

theorem norm_plainMixedSourceMean_sub_le :
    ‖plainMixedSourceMean C outside σ hactual hl houtside hp hAd hout hV false -
      plainMixedSourceMean C outside σ hactual hl houtside hp hAd hout hV true‖ ≤
      plainMixedFrequencyError C outside σ hactual hl houtside hp hAd hout hV :=
  norm_sourceMean_sub_le_frequencyError C outside σ (plainMixedLawMultiplier C outside)
    (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant)
    (mixedQ C.giantCenter C.giant) hactual hl houtside
    (mixedWeight_nonneg C.giantCenter C.giant)
    (fun r _ => mixedDraw_positive C.giantCenter C.giant r)
    (fun r hr => mixed_draw_cells C r
      (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
    hp hAd hout hV false true

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI
