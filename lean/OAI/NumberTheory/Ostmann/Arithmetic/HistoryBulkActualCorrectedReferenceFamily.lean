import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamilyBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamily
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryBulkFibreGiantApproximation
open HistoryGiantOriginalMeanFactorization (Choices)

theorem selected_witness_equality_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
    ∀spectator : PrimeSource,
      (∀p:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∀outside : List ℕ,(∀q∈outside,∃p:spectator.Sample,(p:ℕ)=q) →
    ∀l≤k,∀(a : SelectedNonbulkSample C l)
      (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
      (he : PreservesRemainingBands _ e)(s t : ℤ)(c₁ c₂ : Choices (l:=l) C),
      0<(selectedNonbulkPrior C l).mass a →
      choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c₁≠0 →
      choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c₂≠0 →
    ∀r : Witness C outside a e s t c₁ c₂,
      (∀u,(selectedBulkPrior C l).mass u≠0 → ∀P Q : ℤ,0<P → 0<Q →
        term C outside a e s t c₁ c₂ u P Q=
          fixedReferenceTerm C outside a e he s t c₁ c₂ k r u P Q) ∧
      mixedFibreMean C outside a e s t c₁ c₂=referenceMean C outside a e he s t c₁ c₂ k r := by
  filter_upwards [HistoryBulkIndependentReferenceTerm.selected_ordered_reference_equality_eventually
    d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd spectator hspec outside houtside l hl a e he s t c₁ c₂ ha hc₁ hc₂ r
  have hactual := hL E C hG hcl hcu hb hd spectator hspec
  exact ⟨fun u hu P Q hP hQ=>term_eq_fixedReferenceTerm C outside a e he s t c₁ c₂
    hactual k hl hl ha hc₁ hc₂ houtside r u hu P Q hP hQ,
    mixedFibreMean_eq_referenceMean C outside a e he s t c₁ c₂
      hactual k hl hl ha hc₁ hc₂ houtside r⟩

end Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamily

end

end OAI
