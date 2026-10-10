import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceWeightedMean

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
open Construction Conclusion HistoryGiantReferenceMean HistoryBulkSourceDisintegration Filter
open HistoryGiantOriginalMeanFactorization (Choices)

theorem weighted_fibre_reference_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase → C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀ p : spectator.Sample, Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℕ) ∧
        Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀ (outside : List ℕ), (∀ q∈outside, ∃ p : spectator.Sample, (p:ℕ)=q) →
      ∀ (l K : ℕ), l ≤ K → l ≤ k →
      ∀ (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
        (a : SelectedNonbulkSample C l) (s t : ℤ) (c e : Choices (l:=l) C),
      0 < (selectedNonbulkPrior C l).mass a →
      choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c ≠ 0 →
      choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l e ≠ 0 →
      ∀ J : SelectedBulkSample C l → ℤ → ℤ → ℂ,
      WeightedFixedFibreReference C outside σ a s t c e J K
        (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
        (weightedPrimeFibreMean C outside σ a s t c e J) ∧
      WeightedFixedFibreReference C outside σ a s t c e J K
        (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant)
        (mixedQ C.giantCenter C.giant) (weightedMixedFibreMean C outside σ a s t c e J) := by
  filter_upwards [HistoryBulkFixedReferenceTerm.selected_reference_equality_eventually d Bs BD Bz hk]
    with L hL
  intro E C hG hcl hcu hb hd spectator hspec outside houtside l K hle hl σ a s t c e ha hc he J
  have hactual := hL E C hG hcl hcu hb hd spectator hspec
  exact ⟨weightedPrimeFibreMean_fixed_reference C outside σ a s t c e J
      hactual K hle hl ha hc he houtside,
    weightedMixedFibreMean_fixed_reference C outside σ a s t c e J
      hactual K hle hl ha hc he houtside⟩

end Ostmann.Arithmetic.HistoryBulkFibreOriginalReference

end

end OAI
