import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement
open Construction Conclusion HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryBulkFibreGiantApproximationReference
open HistoryGiantReferenceMean HistoryRepresentativeSourceSeparation Filter
attribute [local instance] Classical.propDecidable

theorem selected_law_errors_eventually (d : Decomposition)
    (Bs BD Bz H : ℝ) {k : ℕ} (hBs : 0≤Bs) (hH : 0≤H) (hk : 2≤k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀q:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (q:ℕ) ∧
        Real.log (q:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∃hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator,
      ∀(outside : List ℕ)(houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
        (hout : outside.length=2*(bulkSize k L/2)),
      ∀l (hl : l≤k),
      ∃(hp : ∀q∈outside,q.Prime)
        (hAd : ∀r : Frame (l:=l) C outside,PairAdmissible r.left r.right outside)
        (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q),
      ∀σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))),
      (primeFrequencyError C outside σ hactual hl houtside hp hAd hout hV ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
        primeFrequencyError C outside σ hactual hl houtside hp hAd hout hV ≤
          Real.exp (-H*(bulkSize k L:ℝ))) ∧
      (plainMixedFrequencyError C outside σ hactual hl houtside hp hAd hout hV ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
        plainMixedFrequencyError C outside σ hactual hl houtside hp hAd hout hV ≤
          Real.exp (-H*(bulkSize k L:ℝ))) ∧
      (‖primeSourceMean C outside σ hactual hl houtside hp hAd hout hV false -
          primeSourceMean C outside σ hactual hl houtside hp hAd hout hV true‖ ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
        ‖primeSourceMean C outside σ hactual hl houtside hp hAd hout hV false -
          primeSourceMean C outside σ hactual hl houtside hp hAd hout hV true‖ ≤
          Real.exp (-H*(bulkSize k L:ℝ))) ∧
      (‖plainMixedSourceMean C outside σ hactual hl houtside hp hAd hout hV false -
          plainMixedSourceMean C outside σ hactual hl houtside hp hAd hout hV true‖ ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
        ‖plainMixedSourceMean C outside σ hactual hl houtside hp hAd hout hV false -
          plainMixedSourceMean C outside σ hactual hl houtside hp hAd hout hV true‖ ≤
          Real.exp (-H*(bulkSize k L:ℝ))) := by
  filter_upwards [selected_frequency_error_eventually d Bs BD Bz H hBs hH hk] with L h
  intro E C hG hGu hcl hcu hb hd spectator hspec
  obtain ⟨hactual,h⟩ := h E C hG hGu hcl hcu hb hd spectator hspec
  refine ⟨hactual,?_⟩
  intro outside houtside hout l hl
  obtain ⟨hp,hAd,hV,h⟩ := h outside houtside hout l hl
  refine ⟨hp,hAd,hV,?_⟩
  intro σ
  have hprime := h σ (primeLawMultiplier C) (PrimeDraw C.giant)
    (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
    (primeWeight_nonneg C.giant) (fun r _ => primeDraw_positive C.giant r)
    (fun r hr => prime_draw_cells C r
      (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr))) false false hl
  have hmixed := h σ (plainMixedLawMultiplier C outside) (MixedDraw C.giantCenter C.giant)
    (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant)
    (mixedQ C.giantCenter C.giant) (mixedWeight_nonneg C.giantCenter C.giant)
    (fun r _ => mixedDraw_positive C.giantCenter C.giant r)
    (fun r hr => mixed_draw_cells C r
      (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr))) false true hl
  have hpmean := norm_primeSourceMean_sub_le C outside σ hactual hl houtside hp hAd hout hV
  have hmmean := norm_plainMixedSourceMean_sub_le C outside σ hactual hl houtside hp hAd hout hV
  exact ⟨hprime,hmixed,⟨hpmean.trans hprime.1,hpmean.trans hprime.2⟩,
    ⟨hmmean.trans hmixed.1,hmmean.trans hmixed.2⟩⟩

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI
