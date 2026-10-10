import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReferenceDisintegration
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReferenceMean

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentFibreReference
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryGiantOriginalMeanFactorization (Choices)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def FixedFibreReference
    (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
    (a : SelectedNonbulkSample C l) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e) (s t : ℤ) (c₁ c₂ : Choices (l:=l) C) (K : ℕ) : Prop :=
  mixedFibreMean C outside a e s t c₁ c₂=0 ∨
    ∃r : Reference C outside a e s t c₁ c₂,
      (∀u,(selectedBulkPrior C l).mass u≠0 → ∀P Q : ℤ,0<P → 0<Q →
        term C outside a e s t c₁ c₂ u P Q=
          fixedReferenceTerm C outside a e he s t c₁ c₂ K r u P Q) ∧
      mixedFibreMean C outside a e s t c₁ c₂=referenceMean C outside a e he s t c₁ c₂ K r

theorem fixed_reference_of_selected_equality
    (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
    (a : SelectedNonbulkSample C l) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e) (s t : ℤ) (c₁ c₂ : Choices (l:=l) C)
    {spectator : PrimeSource}
    (hactual : HistoryBulkIndependentReferenceTerm.SelectedOrderedReferenceEquality C spectator)
    (K : ℕ) (hle : l≤K) (hl : l≤k)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc₁ : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c₁≠0)
    (hc₂ : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c₂≠0)
    (houtside : ∀q∈outside,∃p : spectator.Sample,(p:ℕ)=q) :
    FixedFibreReference C outside a e he s t c₁ c₂ K := by
  rcases mixedFibreMean_eq_zero_or_reference C outside a e s t c₁ c₂ ha with hz | hr
  · exact Or.inl hz
  · let r := Classical.choice hr
    exact Or.inr ⟨r,
      (fun u hu P Q hp hq=>term_eq_fixedReferenceTerm C outside a e he s t c₁ c₂
        hactual K hle hl ha hc₁ hc₂ houtside r u hu P Q hp hq),
      mixedFibreMean_eq_referenceMean C outside a e he s t c₁ c₂
        hactual K hle hl ha hc₁ hc₂ houtside r⟩

def SelectedFibreReferences
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource) : Prop :=
  ∀(outside : List ℕ),(∀q∈outside,∃p : spectator.Sample,(p:ℕ)=q) →
  ∀(l K : ℕ),l≤K → l≤k →
  ∀(a : SelectedNonbulkSample C l)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (he : PreservesRemainingBands _ e)
    (s t : ℤ) (c₁ c₂ : Choices (l:=l) C),
    0 < (selectedNonbulkPrior C l).mass a →
    choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c₁≠0 →
    choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c₂≠0 →
    FixedFibreReference C outside a e he s t c₁ c₂ K

theorem selected_fibre_references_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 → |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) → SelectedFibreReferences C spectator := by
  filter_upwards [HistoryBulkIndependentReferenceTerm.selected_ordered_reference_equality_eventually
    d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd spectator hspec
  have hactual := hL E C hG hcl hcu hb hd spectator hspec
  intro outside houtside l K hle hl a e he s t c₁ c₂ ha hc₁ hc₂
  exact fixed_reference_of_selected_equality C outside a e he s t c₁ c₂
    hactual K hle hl ha hc₁ hc₂ houtside

end Ostmann.Arithmetic.HistoryBulkIndependentFibreReference

end

end OAI
