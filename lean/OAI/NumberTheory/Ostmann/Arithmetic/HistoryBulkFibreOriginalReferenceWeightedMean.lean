import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceWeightedTerm

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
open Construction Conclusion HistoryGiantReferenceMean HistoryBulkSourceDisintegration
open HistoryGiantOriginalMeanFactorization (Choices)
open HistoryBulkFibreReference (originalMean)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l) (s t : ℤ) (c e : Choices (l:=l) C)
variable (J : SelectedBulkSample C l → ℤ → ℤ → ℂ)

def WeightedFixedFibreReference {α : Type*} [Fintype α]
    (K : ℕ) (w : α→ℝ) (P Q : α→ℤ) (mean : ℂ) : Prop :=
  mean=0 ∨ ∃y₀ r₀,
    0 < (selectedBulkPrior C l).mass y₀ ∧ 0 < w r₀ ∧
    weightedFibreTerm C outside σ a s t c e J y₀ (P r₀) (Q r₀)≠0 ∧
    ∃hs : FibreSupported C outside σ a s t c e y₀ (P r₀) (Q r₀),
      (∀y r,(selectedBulkPrior C l).mass y≠0 → w r≠0 →
        weightedFibreTerm C outside σ a s t c e J y (P r) (Q r)=
        weightedFibreReferenceTerm C outside σ a s t c e J K y₀ (P r₀) (Q r₀) hs y (P r) (Q r)) ∧
      mean=originalMean (selectedBulkPrior C l).mass w
        (fun y r=>weightedFibreReferenceTerm C outside σ a s t c e J K y₀ (P r₀) (Q r₀) hs y (P r) (Q r))

theorem weightedWholeFibreMean_fixed_reference
    {spectator : PrimeSource}
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
    (K : ℕ) (hle : l≤K) (hl : l≤k)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c≠0)
    (he : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l e≠0)
    (houtside : ∀q∈outside,∃p : spectator.Sample,(p:ℕ)=q)
    {α : Type*} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
    (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r) :
    WeightedFixedFibreReference C outside σ a s t c e J K w P Q
      (originalMean (selectedBulkPrior C l).mass w
        (fun y r=>weightedFibreTerm C outside σ a s t c e J y (P r) (Q r))) := by
  rcases HistoryBulkFibreReference.originalMean_eq_zero_or_reference
    (selectedBulkPrior C l).mass w
    (fun y r => weightedFibreTerm C outside σ a s t c e J y (P r) (Q r))
    (selectedBulkPrior C l).mass_nonneg hw
    (fun y r => FibreSupported C outside σ a s t c e y (P r) (Q r))
    (fun y r _ _ h => weightedFibreTerm_ne_zero_supported C outside σ a s t c e J y (P r) (Q r) h) with
    hz | ⟨y₀,r₀,hy₀,hr₀,hne,hs⟩
  · exact Or.inl hz
  · have hfixed : ∀y r,(selectedBulkPrior C l).mass y≠0 → w r≠0 →
        weightedFibreTerm C outside σ a s t c e J y (P r) (Q r)=
        weightedFibreReferenceTerm C outside σ a s t c e J K y₀ (P r₀) (Q r₀) hs y (P r) (Q r) := by
      intro y r hy hr
      exact weightedFibreTerm_eq_weightedFibreReferenceTerm C outside σ a s t c e J hactual K hle hl
        y₀ (P r₀) (Q r₀) hs ha hy₀ hc he houtside y (P r) (Q r) hy
        (hpos r hr).1 (hpos r hr).2
    exact Or.inr ⟨y₀,r₀,hy₀,hr₀,hne,hs,hfixed,
      HistoryBulkFibreReference.originalMean_congr _ _ _ _ hfixed⟩

theorem weightedPrimeFibreMean_fixed_reference
    {spectator : PrimeSource}
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
    (K : ℕ) (hle : l≤K) (hl : l≤k)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c≠0)
    (he : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l e≠0)
    (houtside : ∀q∈outside,∃p : spectator.Sample,(p:ℕ)=q) :
    WeightedFixedFibreReference C outside σ a s t c e J K
      (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
      (weightedPrimeFibreMean C outside σ a s t c e J) := by
  rw [weightedPrimeFibreMean_eq_weighted]
  exact weightedWholeFibreMean_fixed_reference C outside σ a s t c e J hactual K hle hl ha hc he
    houtside (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
    (primeWeight_nonneg C.giant) (fun r _=>primeDraw_positive C.giant r)

theorem weightedMixedFibreMean_fixed_reference
    {spectator : PrimeSource}
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
    (K : ℕ) (hle : l≤K) (hl : l≤k)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c≠0)
    (he : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l e≠0)
    (houtside : ∀q∈outside,∃p : spectator.Sample,(p:ℕ)=q) :
    WeightedFixedFibreReference C outside σ a s t c e J K
      (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant)
      (mixedQ C.giantCenter C.giant) (weightedMixedFibreMean C outside σ a s t c e J) := by
  rw [weightedMixedFibreMean_eq_weighted]
  exact weightedWholeFibreMean_fixed_reference C outside σ a s t c e J hactual K hle hl ha hc he
    houtside (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant)
    (mixedQ C.giantCenter C.giant) (mixedWeight_nonneg C.giantCenter C.giant)
    (fun r _=>mixedDraw_positive C.giantCenter C.giant r)

end Ostmann.Arithmetic.HistoryBulkFibreOriginalReference

end

end OAI
