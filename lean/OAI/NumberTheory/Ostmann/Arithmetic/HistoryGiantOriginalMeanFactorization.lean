import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantOriginalMeanFactorizationDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceMeanNonzeroOriginal

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantOriginalMeanFactorization
open Construction Conclusion Filter HistorySignedResidues HistorySignedXiTransport HistorySymbolicEncoding
open HistoryGiantReferenceMean HistoryGiantPriorGrid HistoryGiantXiReplacementActual
open HistoryPairSmoothXi HistoryPairGiantCoordinates

theorem selected_prime_factorization_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 → |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l≤k,
      ∀(x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
        (s t : ℤ)(c e : Choices (l:=l) C),
      (assignmentPrior C.sources _).mass x≠0 → (assignmentPrior C.sources _).mass y≠0 →
      choicesMass C.sources _ _ l c≠0 → choicesMass C.sources _ _ l e≠0 →
      ∀outside : List ℕ,(∀q∈outside,Nat.Prime q) → ∀n : ℕ,
      originalPrimeMean C outside x y s t c e=0 ∨
        ∃r : PrimeDraw C.giant,0 < primeWeight C.giant r ∧
        ∃(hs : (history C x s (primeP C.giant r) (primeQ C.giant r) c).Supported
          (frequencyBound Bs BD Bz k L) outside)
         (gs : (history C y t (primeP C.giant r) (primeQ C.giant r) e).Supported
          (frequencyBound Bs BD Bz k L) outside),
        pairedRealXi (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin
          C.giantCenter _ _ hs gs (pairBackground _ _)≠0 ∧
        originalPrimeMean C outside x y s t c e = compensationFactor C x y s t c e *
          guardedSourcePrimeMean (residueTransform d) (frequencyBound Bs BD Bz k L) outside
            (history C x s (primeP C.giant r) (primeQ C.giant r) c) (history C y t (primeP C.giant r) (primeQ C.giant r) e)
            C.giantCenter ∅ C.giantPositive
            (comparisonModulus _ _ outside n) (pairModulus_dvd_comparisonModulus _ _ _ n)
            (primeScalar C (bulkSize k L/2) _ _ hs gs) := by
  filter_upwards [selected_prime_mean_zero_or_nonzero_reference_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd l hl x y s t c e hx hy hc he outside hout n
  have hh := hL E C hG hcl hcu hb hd l hl x y s t c e hx hy hc he outside hout
    (fun _ Q => counterpart C y Q) (bulkSize k L/2) (bulkSize k L/2) n
    C.scale C.bulkBin C.spectatorBin
  rcases hh with hz | ⟨r,hr,hJ,hne,hs,gs,heq⟩
  · exact Or.inl hz
  · refine Or.inr ⟨r,hr,hs,gs,?_,?_⟩
    · exact pairedRealXi_ne_zero_of_pairXi_ne_zero d _ outside _ _ _ _ _ _ _ _ hs gs hne
    · rw [compensationFactor_eq C x y s t (primeP C.giant r) (primeQ C.giant r) c e]
      exact heq.trans (prime_reference_factor C outside x y s t (primeP C.giant r) (primeQ C.giant r) c e hs gs n)

theorem selected_mixed_factorization_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 → |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l≤k,
      ∀(x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
        (s t : ℤ)(c e : Choices (l:=l) C),
      (assignmentPrior C.sources _).mass x≠0 → (assignmentPrior C.sources _).mass y≠0 →
      choicesMass C.sources _ _ l c≠0 → choicesMass C.sources _ _ l e≠0 →
      ∀outside : List ℕ,(∀q∈outside,Nat.Prime q) → ∀n : ℕ,
      originalMixedMean C outside x y s t c e=0 ∨
        ∃r : MixedDraw C.giantCenter C.giant,0 < mixedWeight C.giantCenter C.giant r ∧
        ∃(hs : (history C x s (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) c).Supported
          (frequencyBound Bs BD Bz k L) outside)
         (gs : (history C y t (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) e).Supported
          (frequencyBound Bs BD Bz k L) outside),
        pairedRealXi (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin
          C.giantCenter _ _ hs gs (pairBackground _ _)≠0 ∧
        originalMixedMean C outside x y s t c e = compensationFactor C x y s t c e *
          guardedSourceMixedMean (residueTransform d) (frequencyBound Bs BD Bz k L) outside
            (history C x s (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) c) (history C y t (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) e)
            C.giantCenter ∅ C.giantPositive
            (comparisonModulus _ _ outside n) (pairModulus_dvd_comparisonModulus _ _ _ n)
            (mixedScalar C (bulkSize k L/2) _ _ hs gs) := by
  filter_upwards [selected_mixed_mean_zero_or_nonzero_reference_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd l hl x y s t c e hx hy hc he outside hout n
  have hh := hL E C hG hcl hcu hb hd l hl x y s t c e hx hy hc he outside hout
    (fun _ Q => counterpart C y Q) (bulkSize k L/2) (bulkSize k L/2) n
    C.scale C.bulkBin C.spectatorBin
  rcases hh with hz | ⟨r,hr,hJ,hne,hs,gs,heq⟩
  · exact Or.inl hz
  · refine Or.inr ⟨r,hr,hs,gs,?_,?_⟩
    · exact pairedRealXi_ne_zero_of_pairXi_ne_zero d _ outside _ _ _ _ _ _ _ _ hs gs hne
    · rw [compensationFactor_eq C x y s t (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) c e]
      exact heq.trans (mixed_reference_factor C outside x y s t (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) c e hs gs n)

end Ostmann.Arithmetic.HistoryGiantOriginalMeanFactorization

end

end OAI
